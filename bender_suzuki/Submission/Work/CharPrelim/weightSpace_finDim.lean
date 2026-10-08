import Submission.Work.CharPrelim.weightSpace_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The weight decomposition in finite dimension

If `k` is an algebraically closed field, `Z` a finite abelian group with `|Z|` invertible in
`k`, `M` a finite-dimensional `k`-vector space and `τ : Z →* Module.End k M`, then the weight
spaces `weightSpace τ χ` span `M`.
-/

noncomputable section

set_option linter.style.haveILetI false

open Classical

namespace Work.CharPrelim

universe u

/-- Auxiliary form of `weightSpace_finDim`, by strong induction on the `k`-dimension. -/
theorem weightSpace_finDim_aux {k : Type*} {Z : Type*} [Field k] [IsAlgClosed k] [CommGroup Z]
    [Finite Z] : ∀ (n : ℕ) (N : Type u) [AddCommGroup N] [Module k N] [FiniteDimensional k N],
      Module.finrank k N = n → ∀ (σ : Z →* Module.End k N),
      IsUnit ((Nat.card Z : ℕ) : k) → (⨆ χ : Z →* kˣ, weightSpace σ χ) = ⊤ := by
  classical
  letI := Fintype.ofFinite Z
  intro n
  refine Nat.strong_induction_on n (fun n ih => ?_)
  intro N _ _ _ hfin σ hcardN
  by_cases hsc : ∃ z : Z, ∀ μ : k, σ z ≠ μ • 1
  · obtain ⟨z, hz⟩ := hsc
    have hz1 : z ^ Nat.card Z = 1 := by
      rw [Nat.card_eq_fintype_card]; exact pow_card_eq_one
    have hpow : (σ z) ^ (Nat.card Z) = 1 := by
      rw [← map_pow, hz1, map_one]
    have htopmu : (⨆ μ : k, (σ z).eigenspace μ) = ⊤ :=
      iSup_eigenspace_eq_top_of_pow_eq_one (σ z) hcardN.ne_zero hpow
    refine le_antisymm le_top ?_
    rw [← htopmu]
    refine iSup_le (fun μ => ?_)
    set W : Submodule k N := (σ z).eigenspace μ with hW
    have hne : W ≠ ⊤ := by
      intro htop
      refine hz μ ?_
      ext x
      have hx : x ∈ W := by rw [htop]; trivial
      rw [hW] at hx
      simpa using (Module.End.mem_eigenspace_iff.mp hx)
    have hfr : Module.finrank k W < Module.finrank k N := by
      have h := Submodule.finrank_lt_finrank_of_lt (s := W) (t := ⊤)
        (lt_top_iff_ne_top.mpr hne)
      rwa [LinearEquiv.finrank_eq Submodule.topEquiv] at h
    have hgen : ∀ (f : Module.End k N) (ν : k), f.eigenspace ν = f.genEigenspace ν 1 := by
      intro f ν; rw [Module.End.genEigenspace_one, Module.End.eigenspace_def]
    have hmaps : ∀ z' : Z, ∀ x ∈ W, σ z' x ∈ W := by
      intro z' x hx
      have hcomm : Commute (σ z) (σ z') := by
        show σ z * σ z' = σ z' * σ z
        rw [← map_mul, ← map_mul, mul_comm]
      have hx' : x ∈ (σ z).genEigenspace μ 1 := by rw [← hgen, ← hW]; exact hx
      have h := Module.End.mapsTo_genEigenspace_of_comm hcomm μ 1 hx'
      rwa [← hgen, ← hW] at h
    have hih : (⨆ χ : Z →* kˣ, weightSpace (restrictRep σ W hmaps) χ) = ⊤ :=
      ih (Module.finrank k W) (by rw [← hfin]; exact hfr) W rfl (restrictRep σ W hmaps) hcardN
    have hmap : Submodule.map W.subtype ⊤ ≤ ⨆ χ : Z →* kˣ, weightSpace σ χ := by
      rw [show (⊤ : Submodule k W) = ⨆ χ : Z →* kˣ, weightSpace (restrictRep σ W hmaps) χ
        from hih.symm]
      rw [Submodule.map_iSup]
      exact iSup_le (fun χ =>
        le_trans (weightSpace_restrictRep_le σ W hmaps χ) (le_iSup (fun χ : Z →* kˣ =>
          weightSpace σ χ) χ))
    rw [Submodule.map_subtype_top] at hmap
    exact hmap
  · push Not at hsc
    by_cases hnt : Nontrivial N
    · choose lam hlam using hsc
      have hxa : ∀ (w : Z) (y : N), σ w y = (lam w) • y := by
        intro w y
        rw [hlam w, LinearMap.smul_apply, Module.End.one_apply]
      have hcomp : ∀ w : Z, σ w⁻¹ * σ w = 1 := by
        intro w
        rw [← map_mul, inv_mul_cancel, map_one]
      have hinj : ∀ w : Z, Function.Injective (σ w) := by
        intro w a b hab
        have h1 := congrArg (σ w⁻¹) hab
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, hcomp w, Module.End.one_apply,
          Module.End.one_apply] at h1
        exact h1
      have hne : ∀ w : Z, lam w ≠ 0 := by
        intro w hw0
        obtain ⟨x, hx⟩ := exists_ne (0 : N)
        have hσ0 : σ w = 0 := by rw [hlam w, hw0, zero_smul]
        refine hx (hinj w ?_)
        rw [hσ0]
        simp
      have hmul : ∀ a b : Z, lam (a * b) = lam a * lam b := by
        intro a b
        obtain ⟨x, hx⟩ := exists_ne (0 : N)
        have h : lam (a * b) • x = (lam a * lam b) • x := by
          calc lam (a * b) • x = σ (a * b) x := (hxa (a * b) x).symm
            _ = σ a (σ b x) := by rw [map_mul, Module.End.mul_apply]
            _ = σ a (lam b • x) := by rw [hxa b x]
            _ = lam b • σ a x := by rw [map_smul]
            _ = lam b • (lam a • x) := by rw [hxa a x]
            _ = (lam a * lam b) • x := by rw [smul_smul, mul_comm]
        have h3 : (lam (a * b) - lam a * lam b) • x = 0 := by
          rw [sub_smul, h, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hx)
      have hone : lam 1 = 1 := by
        obtain ⟨x, hx⟩ := exists_ne (0 : N)
        have h : lam 1 • x = (1 : k) • x := by
          rw [one_smul, ← hxa 1 x, map_one, Module.End.one_apply]
        have h3 : (lam 1 - 1) • x = 0 := by rw [sub_smul, h, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hx)
      let χ : Z →* kˣ :=
      { toFun := fun w => Units.mk0 (lam w) (hne w)
        map_one' := Units.ext (by
          show ((Units.mk0 (lam 1) (hne 1) : kˣ) : k) = ((1 : kˣ) : k)
          rw [Units.val_mk0, hone, Units.val_one])
        map_mul' := fun a b => Units.ext (by
          show ((Units.mk0 (lam (a * b)) (hne (a * b)) : kˣ) : k) =
            ((Units.mk0 (lam a) (hne a) * Units.mk0 (lam b) (hne b) : kˣ) : k)
          rw [Units.val_mk0, Units.val_mul, Units.val_mk0, Units.val_mk0, hmul a b]) }
      have htopp : weightSpace σ χ = ⊤ := by
        rw [Submodule.eq_top_iff']
        intro x
        rw [mem_weightSpace]
        intro w
        show σ w x = ((Units.mk0 (lam w) (hne w) : kˣ) : k) • x
        rw [Units.val_mk0, hxa w x]
      exact le_antisymm le_top (le_iSup_of_le χ (le_of_eq htopp.symm))
    · rw [not_nontrivial_iff_subsingleton] at hnt
      have hsub : (⊥ : Submodule k N) ≤ ⨆ χ : Z →* kˣ, weightSpace σ χ :=
        le_iSup_of_le (1 : Z →* kˣ) (bot_le : (⊥ : Submodule k N) ≤ weightSpace σ 1)
      refine le_antisymm le_top ?_
      intro x _
      refine hsub ?_
      rw [Subsingleton.elim x 0]
      exact Submodule.zero_mem _

/-- **Weight decomposition, finite-dimensional case.**  The weight spaces `weightSpace τ χ`
over the characters `χ : Z →* kˣ` span `M`. -/
theorem weightSpace_finDim {k M Z : Type*} [Field k] [IsAlgClosed k] [CommGroup Z] [Finite Z]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M] (τ : Z →* Module.End k M)
    (hcard : IsUnit ((Nat.card Z : ℕ) : k)) :
    (⨆ (χ : Z →* kˣ), weightSpace τ χ) = ⊤ :=
  weightSpace_finDim_aux (Module.finrank k M) M rfl τ hcard

end Work.CharPrelim
