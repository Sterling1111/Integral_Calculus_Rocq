Require Import Imports.

Notation ℕ := nat.
Notation ℤ := Z.
Notation ℚ := Q.
Notation ℝ := R.

Notation "| x |" := (Rabs x) 
  (at level 200, x at level 0, format "| x |", no associativity) : R_scope.

Notation "√ x" := (sqrt x) (format "√ x", at level 20).

Open Scope R_scope.

Notation "a <= b <= c <= d" := (a <= b /\ b <= c /\ c <= d) 
  (at level 70, b at next level, c at next level, d at next level) : R_scope.
Notation "a < b < c < d" := (a < b /\ b < c /\ c < d) 
  (at level 70, b at next level, c at next level, d at next level) : R_scope.
Notation "a >= b >= c >= d" := (a >= b /\ b >= c /\ c >= d) 
  (at level 70, b at next level, c at next level, d at next level) : R_scope.
Notation "a > b > c > d" := (a > b /\ b > c /\ c > d) 
  (at level 70, b at next level, c at next level, d at next level) : R_scope.
Notation "a = b = c" := (a = b /\ b = c) 
  (at level 70, b at next level, c at next level) : R_scope.
Notation  "a <= b < c <= d" := (a <= b /\ b < c /\ c <= d)
  (at level 70, b at next level, c at next level, d at next level) : R_scope.

Declare Scope interval_scope.
Delimit Scope interval_scope with interval.

Module IntervalNotations.
  Notation "[ a , b ]" := (fun x => a <= x <= b) : interval_scope.
  Notation "[ a , b ⦆" := (fun x => a <= x < b) : interval_scope.
  Notation "⦅ a , b ]" := (fun x => a < x <= b)  : interval_scope.
  Notation "⦅ a , b ⦆" := (fun x => a < x < b) : interval_scope.

  Notation "⦅-∞ , b ⦆" := (fun x => x < b) : interval_scope.
  Notation "⦅ -∞ , b ]" := (fun x => x <= b) : interval_scope.
  Notation "⦅ a , +∞]" := (fun x => a < x) : interval_scope.
  Notation "[ a , +∞⦆" := (fun x => a <= x) : interval_scope.

  Notation "⦅-∞ , +∞⦆" := (Full_set _) : interval_scope.

  Notation "( a , b )" := (fun x => a < x < b) : interval_scope.
  Notation "[ a , b )" := (fun x => a <= x < b) : interval_scope.
  Notation "( a , b ]" := (fun x => a < x <= b) : interval_scope.
End IntervalNotations.