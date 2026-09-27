import Mathlib

/-!
# The general-position condition `hV` in normal-functional form

The counting chapter of the chain route to `Work.Drive.ParityCore γ` reduces its transversality
input (`hV` of `GENERICITY_ASSEMBLY_STATUS.md` §5, `SWEEP_TRANSPORT_NOTES.md` §2) to the following
linear-algebra statement about the *normal functionals* of the planes (`PROJ_IMMERSION_STATUS.md` §6):

> three `3`-planes of `ℝ⁴` through a common line `L = ℝv` meet in exactly `L` **iff** their normal
> functionals are linearly independent.

Mathlib has the *dual* form (`Submodule.dualCoannihilator`, `Subspace.finrank_add_finrank_dualCoannihilator_eq`,
`Submodule.eq_top_of_finrank_eq`) but not the statement itself, so it is proved here.

## Main lemma

For a field `K` and a finite-dimensional `K`-space `F`, a family `φ : ι → (F →ₗ[K] K)` of `#ι = finrank K F`
functionals has

  `(⨅ i, (φ i).ker) = ⊥  ↔  LinearIndependent K φ`,

i.e. the common kernel of a family of *as many* functionals as `finrank F` is trivial exactly when the
family is linearly independent.  This is the criterion that makes `hV` decidable: applied to the
quotient `F = ℝ⁴ ⧸ ℝv` and to the descended normal functionals it says that `W₀ ∩ W₁ ∩ W₂ = ℝv`
iff `φ₀, φ₁, φ₂` are independent.

## Proof

`span (range φ) =: W ≤ Dual K F`; then `⨅ i, (φ i).ker = W.dualCoannihilator` (the common kernel of a
set of functionals is the coannihilator of their span), and for a finite-dimensional space
`W.dualCoannihilator = ⊥ ↔ W = ⊤` (dimension count via
`Subspace.finrank_add_finrank_dualCoannihilator_eq`).  Finally `W = ⊤ ↔ LinearIndependent K φ` because
`#ι = finrank K F = finrank K (Dual K F)` and a family of `finrank`-many vectors spans iff it is
independent (`linearIndependent_iff_card_eq_finrank_span`, `Submodule.eq_top_of_finrank_eq`).

-/

namespace Work.Drive

open Submodule in
/-- **`hV` in normal-functional form.**  For a field `K` with the Orzech property, a
finite-dimensional `K`-space `F` and a family `φ : ι → Dual K F` of `Fintype.card ι = finrank K F`
functionals, the common kernel of the `φ i` is trivial exactly when the family is linearly
independent.

(For `F` of dimension `n` and `ι = Fin n`: `(⨅ i, (φ i).ker) = ⊥ ↔ LinearIndependent K φ`.) -/
theorem iInf_ker_eq_bot_iff_linearIndependent
    {K : Type*} [Field K] [OrzechProperty K]
    {F : Type*} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
    {ι : Type*} [Fintype ι] (φ : ι → (F →ₗ[K] K))
    (h : Fintype.card ι = Module.finrank K F) :
    (⨅ i, (φ i).ker) = ⊥ ↔ LinearIndependent K φ := by
  classical
  set W : Submodule K (Module.Dual K F) := Submodule.span K (Set.range φ) with hW
  have hA : (⨅ i, (φ i).ker) = W.dualCoannihilator := by
    ext v
    rw [Submodule.mem_iInf, Submodule.mem_dualCoannihilator]
    constructor
    · intro hv f hf
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hf
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [LinearMap.mem_ker.mp (hv i), mul_zero]
    · intro hv i
      exact hv (φ i) (Submodule.subset_span ⟨i, rfl⟩)
  have hspanfin : Set.finrank K (Set.range φ) = Module.finrank K ↥W := rfl
  have hdual : Module.finrank K (Module.Dual K F) = Module.finrank K F := Subspace.dual_finrank_eq
  have hbot_top : W.dualCoannihilator = ⊥ ↔ W = ⊤ := by
    constructor
    · intro hbot
      have hadd := Subspace.finrank_add_finrank_dualCoannihilator_eq W
      rw [hbot] at hadd
      rw [finrank_bot, add_zero] at hadd
      exact Submodule.eq_top_of_finrank_eq (hadd.trans hdual.symm)
    · intro htop
      rw [htop, Submodule.eq_bot_iff]
      intro v hv
      have h1 : ∀ f : Module.Dual K F, f v = 0 := fun f =>
        (Submodule.mem_dualCoannihilator v).mp hv f Submodule.mem_top
      have h2 : v ∈ (⊥ : Submodule K F) :=
        (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (⊥ : Submodule K F) v).mp
          (fun φ _ => h1 φ)
      simpa using h2
  rw [hA, hbot_top]
  constructor
  · intro htop
    have hfin : Module.finrank K ↥W = Module.finrank K F := by rw [htop]; simp
    rw [linearIndependent_iff_card_eq_finrank_span, hspanfin, hfin]
    exact h
  · intro hind
    have hcard : Fintype.card ι = Module.finrank K ↥W := by
      rw [← hspanfin]; exact (linearIndependent_iff_card_eq_finrank_span).mp hind
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [← hcard, h, hdual]

open Submodule in
/-- **`hV` in normal-functional form, at the level of `E`.**  Let `v ≠ 0` and let `φ : Fin n → Dual K E`
(`n = finrank K E - 1`) be functionals vanishing on the line `K ∙ v` (they are the normal functionals
of `n` hyperplanes of `E`, all of which contain `K ∙ v`).  Then the common kernel of the `φ i` is
exactly the line `K ∙ v` **iff** the `φ i` are linearly independent.

Applied to `E = ℝ⁴ ⧸ ℝv` (or to `E = ℝ⁴` and `L = ℝv`) this is the general-position condition `hV`
of the counting lane: `W_0 ∩ W_1 ∩ W_2 = ℝv` iff the normal functionals `φ_0, φ_1, φ_2` are
independent. -/
theorem iInf_ker_eq_span_singleton_iff_linearIndependent
    {K : Type*} [Field K] [OrzechProperty K]
    {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    {v : E} (hv : v ≠ 0) {n : ℕ} (φ : Fin n → (E →ₗ[K] K))
    (hφ : ∀ i, φ i v = 0) (hn : n = Module.finrank K E - 1) :
    (⨅ i, (φ i).ker) = K ∙ v ↔ LinearIndependent K φ := by
  classical
  set p : Submodule K E := K ∙ v with hp
  have hp1 : Module.finrank K ↥p = 1 := by rw [hp]; exact finrank_span_singleton hv
  have hle : ∀ i, p ≤ (φ i).ker := fun i => by
    rw [hp]
    exact (Submodule.span_singleton_le_iff_mem v (φ i).ker).mpr (LinearMap.mem_ker.mpr (hφ i))
  have hq : Module.finrank K (E ⧸ p) = n := by
    have h := Submodule.finrank_quotient_add_finrank p
    rw [hp1] at h
    omega
  let ψ : Fin n → (E ⧸ p →ₗ[K] K) := fun i => p.liftQ (φ i) (hle i)
  have hmemψ : ∀ i (x : E), ψ i (p.mkQ x) = φ i x := by
    intro i x
    have h := Submodule.liftQ_mkQ p (φ i) (hle i)
    have h2 := congrArg (fun (L : E →ₗ[K] K) => L x) h
    simpa [ψ] using h2
  have hker : ∀ i (x : E), x ∈ (((ψ i).ker).comap p.mkQ) ↔ x ∈ (φ i).ker := by
    intro i x
    rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.mem_ker, hmemψ]
  have hcomapInf : (⨅ i, (ψ i).ker).comap p.mkQ = ⨅ i, (φ i).ker := by
    rw [Submodule.comap_iInf]
    exact iInf_congr (fun i => Submodule.ext (hker i))
  have hmkQ0 : ∀ x : E, p.mkQ x = 0 ↔ x ∈ p := fun x => by
    rw [Submodule.mkQ_apply]; exact Submodule.Quotient.mk_eq_zero p
  have hcomap : (⨅ i, (ψ i).ker).comap p.mkQ = p ↔ (⨅ i, (ψ i).ker) = ⊥ := by
    constructor
    · intro h
      ext y
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective p y
      rw [Submodule.mem_bot, ← Submodule.mem_comap, h, hmkQ0]
    · intro h
      ext x
      rw [Submodule.mem_comap, h, Submodule.mem_bot, hmkQ0]
  have hmain := iInf_ker_eq_bot_iff_linearIndependent ψ (by rw [Fintype.card_fin, hq])
  have hsum : ∀ g : Fin n → K, (∑ i, g i • ψ i) = 0 ↔ (∑ i, g i • φ i) = 0 := by
    intro g
    constructor
    · intro hg
      refine LinearMap.ext (fun x => ?_)
      have h1 : (∑ j, g j • φ j) x = (∑ j, g j • ψ j) (p.mkQ x) := by
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl (fun j _ => by rw [hmemψ j x])
      rw [h1, hg]
      simp
    · intro hg
      refine LinearMap.ext (fun x => ?_)
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective p x
      have h1 : (∑ j, g j • ψ j) (p.mkQ y) = (∑ j, g j • φ j) y := by
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl (fun j _ => by rw [hmemψ j y])
      rw [h1, hg]
      simp
  have hLI : LinearIndependent K ψ ↔ LinearIndependent K φ := by
    rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
    exact ⟨fun h g hg => h g ((hsum g).mpr hg), fun h g hg => h g ((hsum g).mp hg)⟩
  rw [← hcomapInf, hcomap, hmain]
  exact hLI

/-- **The dimension of the common kernel of a family of functionals.**  For a finite family
`φ : ι → Dual K F` with `#ι ≤ finrank K F`, the common kernel `⨅ i, (φ i).ker` has dimension
`finrank K F - #ι` exactly when the family is linearly independent.  (This is the "hyperplane"
form of `iInf_ker_eq_bot_iff_linearIndependent`: applied to `E = ℝ⁴` it says that `n` hyperplanes of
`ℝ⁴` meet in a subspace of dimension `4 - n` iff their normal functionals are independent.)

The proof is the rank-nullity count for the common kernel: the annihilator of `⨅ i, (φ i).ker` is the
span of the `φ i` (`Subspace.dualAnnihilator_iInf_eq` for the inclusion `⊆`
`mem_span_of_iInf_ker_le_ker`, and `φ i ∈ (⨅ j, (φ j).ker).dualAnnihilator` for the reverse one), so
`finrank (⨅ i, (φ i).ker) + finrank (span (range φ)) = finrank K F`
(`Subspace.finrank_add_finrank_dualAnnihilator_eq`), and
`finrank (span (range φ)) = #ι ↔ LinearIndependent K φ`
(`linearIndependent_iff_card_eq_finrank_span`). -/
theorem finrank_iInf_ker_eq_iff_linearIndependent
    {K : Type*} [Field K] [OrzechProperty K]
    {F : Type*} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
    {ι : Type*} [Fintype ι] (φ : ι → (F →ₗ[K] K))
    (h : Fintype.card ι ≤ Module.finrank K F) :
    Module.finrank K ↥(⨅ i, (φ i).ker) = Module.finrank K F - Fintype.card ι ↔
      LinearIndependent K φ := by
  have hann : (⨅ i, (φ i).ker).dualAnnihilator = Submodule.span K (Set.range φ) := by
    refine le_antisymm ?_ ?_
    · intro f hf
      refine mem_span_of_iInf_ker_le_ker (L := φ) (K := f) fun x hx => ?_
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (⨅ i, (φ i).ker) x).mpr hx f hf
    · refine Submodule.span_le.mpr ?_
      rintro f ⟨i, rfl⟩
      exact (Submodule.mem_dualAnnihilator (φ i)).mpr fun x hx =>
        LinearMap.mem_ker.mp ((Submodule.mem_iInf (fun j => (φ j).ker)).mp hx i)
  have hAB : Module.finrank K ↥(⨅ i, (φ i).ker)
      + Module.finrank K ↥(Submodule.span K (Set.range φ)) = Module.finrank K F := by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq (⨅ i, (φ i).ker)
    rwa [hann] at this
  rw [linearIndependent_iff_card_eq_finrank_span]
  constructor
  · intro hfin
    change Fintype.card ι = Module.finrank K ↥(Submodule.span K (Set.range φ))
    exact (Nat.add_left_cancel
      ((show Module.finrank K F - Fintype.card ι
          + Module.finrank K ↥(Submodule.span K (Set.range φ)) = Module.finrank K F from by
            rw [← hfin]; exact hAB).trans (Nat.sub_add_cancel h).symm)).symm
  · intro hind
    have hthis : Fintype.card ι = Module.finrank K ↥(Submodule.span K (Set.range φ)) := by
      simpa only [Set.finrank] using hind
    exact Nat.eq_sub_of_add_eq (by rw [hthis]; exact hAB)

end Work.Drive
