import Mathlib
import Submission.Work.WilG4c.IteFamGraphMem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- General-`m` version of `IteFamGraphMem`: the family member `G i` agrees with `F i` on the
parameter set `Λ` and equals the constant `c` outside `Λ`; if `Λ` and `famGraph (F i)` are
`Ω`-bounded then so is `famGraph (G i)`, with format and degree growing additively. -/
theorem IteFamGraphMemGen (S : WilkiesDesign.SOMin) {p m k : ℕ} (Λ : Set (Fin p → ℝ)) (c : ℝ)
    (F G : Work.WilkG4c.Family k p m) (i : Fin k) (aΛ dP F0 D : ℕ)
    (hΛ : Λ ∈ S.Ω aΛ dP p)
    (hF : WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + m + 1))
    (hG : ∀ l t, l ∈ Λ → G i l t = F i l t)
    (hGc : ∀ l t, l ∉ Λ → G i l t = c) :
    WilkiesDesign.CG.famGraph (G i) ∈
      S.Ω (F0 + aΛ + 3 * (p + m + 1) + 3 * p + 6) (D + 2 * dP + 5) (p + m + 1) := by
  rw [famGraph_ite_eq (m := m) Λ c (F i) (G i) hG hGc]
  -- the parameter set, in the coordinates of `famGraph`
  have hA0 : parSet p m Λ ∈
      S.Ω (max (aΛ + (p + m)) ((p + m) + p) + 1 + p) (dP + 2) (p + m) :=
    parSet_mem S hΛ
  have hA1 : {z : Fin (p + m + 1) → ℝ | Fin.init z ∈ parSet p m Λ} ∈
      S.Ω (max (aΛ + (p + m)) ((p + m) + p) + 1 + p + 1) (dP + 2)
        (p + m + 1) :=
    S.prod_right hA0
  -- a common format for the four pieces
  have hF' : famGraph (F i) ∈
      S.Ω (F0 + aΛ + 3 * (p + m + 1) + 3 * p + 4) D (p + m + 1) :=
    Work.WilG0.Omega_mono_F (by omega) hF
  have hA' : {z : Fin (p + m + 1) → ℝ | Fin.init z ∈ parSet p m Λ} ∈
      S.Ω (F0 + aΛ + 3 * (p + m + 1) + 3 * p + 4) (dP + 2) (p + m + 1) := by
    refine Work.WilG0.Omega_mono_F ?_ hA1
    have hm : max (aΛ + (p + m)) ((p + m) + p) ≤
        (aΛ + (p + m)) + ((p + m) + p) :=
      max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    omega
  have hAc' : ({z : Fin (p + m + 1) → ℝ | Fin.init z ∈ parSet p m Λ})ᶜ ∈
      S.Ω (F0 + aΛ + 3 * (p + m + 1) + 3 * p + 4) (dP + 2) (p + m + 1) := by
    refine Work.WilG0.Omega_mono_F ?_ (S.compl hA1)
    have hm : max (aΛ + (p + m)) ((p + m) + p) ≤
        (aΛ + (p + m)) + ((p + m) + p) :=
      max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    omega
  have hH : {z : Fin (p + m + 1) → ℝ | z (Fin.last (p + m)) = c} ∈
      S.Ω (F0 + aΛ + 3 * (p + m + 1) + 3 * p + 4) 1 (p + m + 1) :=
    Work.WilG0.Omega_mono_FD (by omega) (by omega) (lastCoord_eq_mem S (p + m) c)
  -- the two intersections and the union
  have hI1 : famGraph (F i) ∩
      {z : Fin (p + m + 1) → ℝ | Fin.init z ∈ parSet p m Λ} ∈
      S.Ω (F0 + aΛ + 3 * (p + m + 1) + 3 * p + 5) (D + (dP + 2)) (p + m + 1) :=
    Work.WilG0.Omega_inter2 hF' hA'
  have hI2 : ({z : Fin (p + m + 1) → ℝ | Fin.init z ∈ parSet p m Λ})ᶜ ∩
      {z : Fin (p + m + 1) → ℝ | z (Fin.last (p + m)) = c} ∈
      S.Ω (F0 + aΛ + 3 * (p + m + 1) + 3 * p + 5) ((dP + 2) + 1)
        (p + m + 1) :=
    Work.WilG0.Omega_inter2 hAc' hH
  have hU : (famGraph (F i) ∩
      {z : Fin (p + m + 1) → ℝ | Fin.init z ∈ parSet p m Λ}) ∪
      (({z : Fin (p + m + 1) → ℝ | Fin.init z ∈ parSet p m Λ})ᶜ ∩
        {z : Fin (p + m + 1) → ℝ | z (Fin.last (p + m)) = c}) ∈
      S.Ω (F0 + aΛ + 3 * (p + m + 1) + 3 * p + 5)
        ((D + (dP + 2)) + ((dP + 2) + 1)) (p + m + 1) :=
    Work.WilG0.Omega_union2 hI1 hI2
  exact Work.WilG0.Omega_mono_FD (by omega) (by omega) hU

end Work.WilG4c
