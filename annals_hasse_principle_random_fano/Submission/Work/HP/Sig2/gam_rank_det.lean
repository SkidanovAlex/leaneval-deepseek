import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDBasic.mem_Gam_iff
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.Lat.detL_ge_one

/-!
# Rank and determinant of `Γ_{x,y} = Gam d n x y`

`Γ_{x,y} = Λ_{ν(x)} ∩ Λ_{ν(y)} ⊆ ℤ^{N_{d,n}}` is the lattice of coefficient vectors `a` with
`f_a(x) = f_a(y) = 0`; equivalently it is the kernel of the pair of linear forms
`Φ_{x,y} : a ↦ (⟨a, ν(x)⟩, ⟨a, ν(y)⟩)`, a linear map into `ℤ²`.

Assuming `ν_{d,n}(x)` and `ν_{d,n}(y)` are `ℤ`-linearly independent:

* **rank.**  Rank–nullity over `ℤ` gives `finrank Γ = N_{d,n} - finrank (range Φ) ≥ N_{d,n} - 2`,
  while the rank-`2` sublattice `L = ℤ ν(x) ⊕ ℤ ν(y)` is a complement to `Γ` (`L ⊓ Γ = ⊥`),
  giving `finrank Γ ≤ N_{d,n} - 2`.  Hence `rk Γ = N_{d,n} - 2`.
* **determinant.**  `detL L ≥ 1 > 0` for *every* integral lattice (`Work.HP.Lat.detL_ge_one`).
-/

set_option autoImplicit false

noncomputable section

open Work.HP

namespace Work.HP.Sig2

/-- The pair of linear forms `Φ_{x,y}(a) = (⟨a, ν_{d,n}(x)⟩, ⟨a, ν_{d,n}(y)⟩)`, whose kernel is
`Gam d n x y`. -/
noncomputable def pairForm (d n : ℕ) (x y : Fin (n + 1) → ℤ) :
    (Mon d n → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) :=
  LinearMap.pi (fun i : Fin 2 =>
    if i = 0 then Fintype.linearCombination ℤ (veronese d n x)
    else Fintype.linearCombination ℤ (veronese d n y))

/-- `⟨a, ν_{d,n}(x)⟩` is `formEval d n a x`. -/
theorem linearCombination_veronese_eq_formEval (d n : ℕ) (x : Fin (n + 1) → ℤ)
    (a : Mon d n → ℤ) :
    Fintype.linearCombination ℤ (veronese d n x) a = formEval d n a x := by
  simp [formEval, Fintype.linearCombination_apply]

/-- Membership in the kernel of `Φ_{x,y}`: vanishing of the two linear forms. -/
theorem mem_pairForm_ker_iff (d n : ℕ) (x y : Fin (n + 1) → ℤ) (a : Mon d n → ℤ) :
    a ∈ (pairForm d n x y).ker ↔ formEval d n a x = 0 ∧ formEval d n a y = 0 := by
  rw [LinearMap.mem_ker, funext_iff, Fin.forall_fin_two]
  simp only [Pi.zero_apply]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨by simpa [pairForm, linearCombination_veronese_eq_formEval] using h0,
           by simpa [pairForm, linearCombination_veronese_eq_formEval] using h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨by simpa [pairForm, linearCombination_veronese_eq_formEval] using h0,
           by simpa [pairForm, linearCombination_veronese_eq_formEval] using h1⟩

/-- `Gam d n x y` is the kernel of the pair of linear forms `Φ_{x,y}`. -/
theorem Gam_eq_pairForm_ker (d n : ℕ) (x y : Fin (n + 1) → ℤ) :
    Gam d n x y = (pairForm d n x y).ker :=
  Submodule.ext fun a => by
    rw [Work.HP.MDBasic.mem_Gam_iff, mem_pairForm_ker_iff]

/-- The `ℤ`-version of `Submodule.finrank_sup_add_finrank_inf_eq` (the modularity formula for
submodules of `ℤ^ι`), obtained from the cardinal-valued `Submodule.rank_sup_add_rank_inf_eq`
by `Module.finrank_eq_rank`. -/
theorem finrank_sup_add_finrank_inf_eq_int {ι : Type*} [Fintype ι]
    (s t : Submodule ℤ (ι → ℤ)) :
    Module.finrank ℤ ↥(s ⊔ t) + Module.finrank ℤ ↥(s ⊓ t)
      = Module.finrank ℤ ↥s + Module.finrank ℤ ↥t := by
  have h := Submodule.rank_sup_add_rank_inf_eq s t
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank,
      ← Module.finrank_eq_rank] at h
  exact_mod_cast h

theorem gam_rank_det (d n : ℕ) (x y : Fin (n + 1) → ℤ)
    (hxy : LinearIndependent ℤ ![veronese d n x, veronese d n y]) :
    rk (Gam d n x y) = NN d n - 2 ∧ 0 < detL (Gam d n x y) := by
  classical
  set A : Mon d n → ℤ := veronese d n x with hA
  set B : Mon d n → ℤ := veronese d n y with hB
  set Φ : (Mon d n → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) := pairForm d n x y with hΦ
  have hGam : Gam d n x y = Φ.ker := by rw [hΦ]; exact Gam_eq_pairForm_ker d n x y
  -- ### rank–nullity for `Φ`
  have hrn := Submodule.finrank_quotient_add_finrank (R := ℤ) (M := Mon d n → ℤ) Φ.ker
  rw [LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange Φ)] at hrn
  have hM : Module.finrank ℤ (Mon d n → ℤ) = NN d n := by
    rw [Module.finrank_fintype_fun_eq_card]
  have hle2 : Module.finrank ℤ ↥Φ.range ≤ 2 := by
    have h := Submodule.finrank_le (R := ℤ) (M := Fin 2 → ℤ) Φ.range
    rwa [Module.finrank_fin_fun] at h
  -- ### lower bound `NN - 2 ≤ finrank (ker Φ)`
  have hlow : NN d n - 2 ≤ Module.finrank ℤ ↥Φ.ker := by
    rw [hM] at hrn
    omega
  -- ### the rank-`2` complement `L = ℤ A ⊕ ℤ B`
  set L : Submodule ℤ (Mon d n → ℤ) := Submodule.span ℤ ({A, B} : Set (Mon d n → ℤ)) with hL
  have hind : LinearIndependent ℤ ![A, B] := hxy
  have hLrank : Module.finrank ℤ ↥L = 2 := by
    have hrange : (Set.range ![A, B]) = ({A, B} : Set (Mon d n → ℤ)) := by
      ext z; constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp
      · intro hz; rcases hz with hz | hz
        · exact ⟨0, by simpa using hz.symm⟩
        · exact ⟨1, by simpa using hz.symm⟩
    rw [hL, ← hrange, finrank_span_eq_card hind, Fintype.card_fin]
  -- `L ⊓ ker Φ = ⊥`
  have hdisj : L ⊓ Φ.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro a ha
    rw [Submodule.mem_inf] at ha
    obtain ⟨haL, haK⟩ := ha
    rw [Submodule.mem_span_pair] at haL
    obtain ⟨s, t, hst⟩ := haL
    rw [hΦ, mem_pairForm_ker_iff] at haK
    obtain ⟨hfA, hfB⟩ := haK
    -- the combination form of `a`
    have hpt : ∀ m, a m = s * A m + t * B m := by
      intro m
      have h := congrFun hst m
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
      exact h.symm
    -- the two pairings against `A` and `B` vanish
    have hAA : dotZ A a = 0 := by
      rw [dotZ_apply, Finset.sum_congr rfl (fun m _ => mul_comm (A m) (a m))]
      simpa [formEval] using hfA
    have hBB : dotZ B a = 0 := by
      rw [dotZ_apply, Finset.sum_congr rfl (fun m _ => mul_comm (B m) (a m))]
      simpa [formEval] using hfB
    -- hence `⟨a,a⟩ = 0`
    have hkey : dotZ a a = s * dotZ A a + t * dotZ B a := by
      rw [dotZ_apply, dotZ_apply, dotZ_apply]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _
      rw [hpt m]; ring
    rw [hAA, hBB, mul_zero, mul_zero, add_zero] at hkey
    -- a nonnegative sum vanishing termwise
    funext m
    have hm : a m * a m = 0 := by
      rw [dotZ_apply] at hkey
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => mul_self_nonneg (a m))).mp hkey m
        (Finset.mem_univ m)
    exact mul_self_eq_zero.mp hm
  -- ### upper bound `finrank (ker Φ) ≤ NN - 2`
  have hsup : Module.finrank ℤ ↥(L ⊔ Φ.ker) = 2 + Module.finrank ℤ ↥Φ.ker := by
    have h := finrank_sup_add_finrank_inf_eq_int L Φ.ker
    rw [hdisj, finrank_bot, hLrank, add_zero] at h
    omega
  have hsupLe : Module.finrank ℤ ↥(L ⊔ Φ.ker) ≤ NN d n := by
    have h := Submodule.finrank_le (R := ℤ) (M := Mon d n → ℤ) (L ⊔ Φ.ker)
    rwa [hM] at h
  have hhigh : Module.finrank ℤ ↥Φ.ker ≤ NN d n - 2 := by
    rw [hsup] at hsupLe
    omega
  -- ### conclude
  have hfin : Module.finrank ℤ ↥Φ.ker = NN d n - 2 := le_antisymm hhigh hlow
  constructor
  · rw [Work.HP.rk, hGam]
    exact hfin
  · have h1 : (1 : ℝ) ≤ detL (Gam d n x y) := Work.HP.Lat.detL_ge_one _
    linarith

end Work.HP.Sig2
