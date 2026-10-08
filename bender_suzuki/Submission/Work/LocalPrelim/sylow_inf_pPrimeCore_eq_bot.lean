import Mathlib
import Submission.Work.LocalPrelim.Defs
import Submission.Work.Fitting.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A Sylow `p`-subgroup meets the `p'`-core trivially

`O_{p'}(X)` is a `p'`-group and any Sylow `p`-subgroup `P` is a `p`-group, so the
intersection `P ⊓ O_{p'}(X)` has order dividing both a `p`-power and a `p'`-number:
its order is `1`.

This is used, e.g., in the analysis of sections `K/H` of odd-order groups where
`O_{p'}` is the relevant normal subgroup.
-/

namespace Work.LocalPrelim

open Work.Fitting

theorem sylow_inf_pPrimeCore_eq_bot {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (P : Sylow p X) : (P : Subgroup X) ⊓ Work.Fitting.pPrimeCore p X = ⊥ := by
  set K : Subgroup X := (P : Subgroup X) ⊓ Work.Fitting.pPrimeCore p X with hK
  -- `P` has cardinality a power of `p`.
  have hPn : Work.Fitting.IsPiNat (fun q => q = p) (Nat.card ↥(P : Subgroup X)) :=
    (Work.Fitting.isPiNat_prime_iff_isPGroup hp (P : Subgroup X)).mpr P.isPGroup'
  -- `O_{p'}(X)` has cardinality a `p'`-number.
  have hOn : Work.Fitting.IsPiNat (fun q => q ≠ p)
      (Nat.card ↥(Work.Fitting.pPrimeCore p X)) :=
    Work.Fitting.piCore_isPiNat X (fun q => q ≠ p)
  -- Hence `|K|` divides both, so is a `p`-number and a `p'`-number.
  have hKp : Work.Fitting.IsPiNat (fun q => q = p) (Nat.card ↥K) :=
    Work.Fitting.isPiNat_of_dvd (Subgroup.card_dvd_of_le inf_le_left) hPn
  have hKq : Work.Fitting.IsPiNat (fun q => q ≠ p) (Nat.card ↥K) :=
    Work.Fitting.isPiNat_of_dvd (Subgroup.card_dvd_of_le inf_le_right) hOn
  -- So a prime divisor of `|K|` would be both `p` and not `p`.
  have hcard : Nat.card ↥K = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
    exact (hKq q hq hqdvd) (hKp q hq hqdvd)
  exact Subgroup.card_eq_one.mp hcard

end Work.LocalPrelim
