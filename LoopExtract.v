Require Import Sail2_values Sail2_prompt_monad Sail2_prompt.
From Ltac2 Require Import Ltac2 Std Message.
From Ltac2 Require Constr.

Ltac2 fixdeltafn x := { rBeta := false; rMatch := false; rFix := true; rCofix := false; rZeta := false; rDelta := true; rConst := [x] }.
Ltac2 betafl := { rBeta := true; rMatch := false; rFix := false; rCofix := false; rZeta := false; rDelta := false; rConst := [] }.

(* cbn is good for fixpoints, terrible for lone definitions *)
Ltac2 loop_body fn appliedfn :=
  let fnbody := eval_cbn (fixdeltafn fn) appliedfn in
(*  let fnbody := eval hnf in fnbody in  TODO: hnf is too much *)
  let rec aux t :=
    print (of_string "aux");
    print (of_constr t);
    (* TODO somehow try to keep original variable names *)
    (*let x1 := fresh "x1" in
    let x2 := fresh "x2" in*)
    lazy_match! t with
    | context [whileMT ?vars _ _ ?body] => print (of_string "HELLO"); body
    | context [untilMT ?vars _ _ ?body] => body
    | fun _ => ?x => aux x
    | (fun x1 : ?ty => @?x x1) =>
      constr:(fun (x1 : $ty) =>
                ltac2:(let t := eval_cbv betafl (Constr.Unsafe.make (Constr.Unsafe.App x (Array.make 1 (&x1)))) in
                       let r := (aux t) in
                       exact $r))
(*
  | (fix foo (x1 : ?T1) (x2 : ?T2 x1) {struct x2} := @?X x1 x2) =>
      constr:(fun (x1 : T1) (x2 : T2 x1) =>
        ltac:(let t := eval cbv beta in (X x1 x2) in
              let r := (aux t) in
              exact r))*)
    | bind ?m ?f => Control.plus (fun () => aux m) (fun _ => aux f)
    | bind0 ?m1 ?m2 => Control.plus (fun () => aux m1) (fun _ => aux m2)
    | try_catch ?m ?h => Control.plus (fun () => aux m) (fun _ => aux h)
    | catch_early_return ?m => aux m
    | liftR ?m => aux m
    | try_catchR ?m ?h => Control.plus (fun () => aux m) (fun _ => aux h)
    | let x1 := ?t1 in @?x x1 =>
      let ty1 := Constr.type t1 in
      constr:(fun (x1 : $ty1) =>
        ltac2:(let t := eval_cbv betafl '($x &x1) in
               let r := (aux t) in
               exact $r))
    | let '(x1, x2) := ?t0 in @?x x1 x2 =>
      let ty0 := Constr.type t0 in
      match! ty0 with prod ?ty1 ?ty2 =>
      constr:(fun (x1 : $ty1) (x2 : $ty2) =>
        ltac2:(print (of_constr x);
               let args := Array.make 2 (&x1) in
               Array.set args 1 (&x2);
               let tm := (Constr.Unsafe.make (Constr.Unsafe.App x args)) in
               let t := eval_cbv betafl tm in
               let r := (aux t) in
               exact $r))
end
    | let '(existT _ x1 x2) := ?t0 in @?x x1 x2 =>
        let ty0 := Constr.type t0 in
        print (of_string "existT type");
        print (of_constr ty0);
        match! ty0 with @sigT ?ty ?p =>
          print (of_string "let existT types");
          print (of_constr ty);
          print (of_constr p);
      constr:(fun (x1 : $ty) (x2 : $p x1) (*: $ty2*) =>
        ltac2:(let args := Array.make 2 (&x1) in
               Array.set args 1 (&x2);
               let tm := (Constr.Unsafe.make (Constr.Unsafe.App x args)) in
               let t := eval_cbv betafl tm in
               let r := (aux t) in
               exact $r))
end
    | if ?g then ?t1 else ?t2 => Control.plus (fun () => aux t1) (fun _ => aux t2)
    | match _ with left x1 => @?b1 x1 | right x2 => @?b2 x2 end =>
      Control.plus (fun () =>
        let ty := Constr.type &x1 in
        constr:(fun x1 : $ty =>
          ltac2:(let t := eval_cbv betafl (Constr.Unsafe.make (Constr.Unsafe.App b1 (Array.make 1 (&x1)))) in
                 let r := (aux t) in
                 exact $r)))
                   (fun ex_ => print (of_exn ex_);
        let ty := Constr.type &x2 in
print (of_string "type");
print (of_constr ty);
        constr:(fun x2 : $ty =>
          ltac2:(let t := eval_cbv betafl (Constr.Unsafe.make (Constr.Unsafe.App b2 (Array.make 1 (&x2)))) in
                 let r := (aux t) in
                 exact $r)))
(*    | ?x _ => (*idtac "app" x;*) fail
    | _ =>
      match! t with
      | ?x => is_var x; idtac "var"
      | ?x => let ty := type of x in idtac "mystery term" x "of type" ty
      end*)
    end in
  print (of_constr (aux fnbody)).
