import Mathlib
import Submission.Work.Tower.ProPEndgame.Defs

namespace Work.Tower.ProPEndgame

open scoped Classical

/-- The canonical map `relVsMk p R : R → relVs p R` sends `1` to `0`. -/
private theorem relVsMk_one (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) :
    relVsMk p R (1 : R) = 0 := by
  show QuotientAddGroup.mk (Additive.ofMul (Abelianization.of (G := R) 1)) = 0
  simp

/-- The canonical map `relVsMk p R : R → relVs p R` is compatible with inverses. -/
private theorem relVsMk_inv (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) (r : R) :
    relVsMk p R r⁻¹ = - relVsMk p R r := by
  have h := relVsMk_mul p R r r⁻¹
  rw [mul_inv_cancel, relVsMk_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Let `φ : F_d ↠ G` be a presentation of a finite group and let `V = R/([R,R]·[R,F]·R^p)` be
the `𝔽_p`-vector space `Work.Tower.ProPEndgame.relVs p R` for `R = ker φ`, of dimension
`Work.Tower.ProPEndgame.relRank p R`.  Then there is a family of `relRank p R` elements of `R`
whose images generate `V`; equivalently whose normal closure together with `relFt p R` is all of
`R`.

Proof.  `R` has finite index in the finitely generated free group `F_d` (its index is `|G|`), hence
is finitely generated; so `V` is a finitely generated module over the field `𝔽_p` and has a basis
(`Module.finBasis`).  The canonical map `relVsMk p R : R → V` is surjective, so each basis vector
is the image of some `f i ∈ R`.  For `r ∈ R` the class of `r` in `V` is `∑ cᵢ • (class of f i)`
with `cᵢ ∈ ZMod p`, which by `relVsMk_mul` and `relVsMk_pow` equals the class of
`∏ᵢ f i ^ (cᵢ).val`; hence `relVsMk (r * (∏ᵢ f i ^ (cᵢ).val)⁻¹) = 0`, and `relVsMk_eq_zero_iff`
gives `r * (∏ᵢ f i ^ (cᵢ).val)⁻¹ ∈ relFt p R`.  Therefore
`normalClosure (range f) ⊔ relFt p R = R` (the reverse inclusion is clear since `range f ⊆ R` and
`relFt p R ≤ R`). -/
theorem exists_generating_family (p : ℕ) [Fact p.Prime] {d : ℕ} {G : Type} [Group G] [Finite G]
    (φ : FreeGroup (Fin d) →* G) (hφ : Function.Surjective φ) :
    ∃ f : Fin (Work.Tower.ProPEndgame.relRank p φ.ker) → φ.ker,
      Subgroup.normalClosure (Set.range (fun i => ((f i : φ.ker) : FreeGroup (Fin d))))
        ⊔ Work.Tower.ProPEndgame.relFt p φ.ker = φ.ker := by
  classical
  -- `R = ker φ` has finite index in the finitely generated group `F_d`, hence is finitely
  -- generated.
  have hFin : Finite (FreeGroup (Fin d) ⧸ φ.ker) :=
    Finite.of_surjective _ (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.surjective
  have hIdx : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hFG : Group.FG φ.ker := inferInstance
  obtain ⟨S, hS⟩ := hFG.out
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- the images of a finite generating set of `R` span the `𝔽_p`-vector space `V`
  have hmem : ∀ r : φ.ker, relVsMk p φ.ker r ∈
      Submodule.span (ZMod p) (↑(S.image (relVsMk p φ.ker)) : Set (relVs p φ.ker)) := by
    intro r
    have hr : r ∈ Subgroup.closure (↑S : Set φ.ker) := by rw [hS]; exact Subgroup.mem_top r
    induction hr using Subgroup.closure_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    | one => rw [relVsMk_one]; exact Submodule.zero_mem _
    | mul x y hx hy ihx ihy => rw [relVsMk_mul]; exact Submodule.add_mem _ ihx ihy
    | inv x hx ihx => rw [relVsMk_inv]; exact Submodule.neg_mem _ ihx
  have hspan : Submodule.span (ZMod p) (↑(S.image (relVsMk p φ.ker)) : Set (relVs p φ.ker)) = ⊤ :=
    eq_top_iff.mpr (fun x _ => by obtain ⟨r, rfl⟩ := relVsMk_surjective p φ.ker x; exact hmem r)
  -- so `V` is a finite-dimensional `𝔽_p`-module, with a basis indexed by `Fin (relRank p R)`
  haveI : Module.Finite (ZMod p) (relVs p φ.ker) := ⟨⟨S.image (relVsMk p φ.ker), hspan⟩⟩
  let b : Module.Basis (Fin (relRank p φ.ker)) (ZMod p) (relVs p φ.ker) :=
    Module.finBasis (ZMod p) (relVs p φ.ker)
  -- lift each basis vector along the surjection `relVsMk`
  have hb : ∀ i : Fin (relRank p φ.ker), ∃ r : φ.ker, relVsMk p φ.ker r = b i :=
    fun i => relVsMk_surjective p φ.ker (b i)
  choose f hf using hb
  refine ⟨f, le_antisymm ?_ ?_⟩
  · -- the normal closure of the `f i` together with `relFt` stays inside `R = ker φ`
    apply sup_le
    · apply Subgroup.normalClosure_le_normal
      rintro x ⟨i, rfl⟩
      exact (f i).2
    · exact relFt_le p φ.ker inferInstance
  · -- conversely everything in `R` is reached
    let H : Subgroup (FreeGroup (Fin d)) :=
      Subgroup.normalClosure (Set.range fun i => ((f i : φ.ker) : FreeGroup (Fin d)))
        ⊔ relFt p φ.ker
    change ∀ x ∈ φ.ker, x ∈ H
    intro r hr
    -- the image of `H` in `V` is a submodule containing a basis, hence everything
    let P : Submodule (ZMod p) (relVs p φ.ker) :=
      { carrier := { x | ∃ h : φ.ker, ((h : φ.ker) : FreeGroup (Fin d)) ∈ H ∧ relVsMk p φ.ker h = x }
        zero_mem' := ⟨1, by simp, relVsMk_one p φ.ker⟩
        add_mem' := by
          rintro x y ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
          refine ⟨a * c, ?_, by rw [relVsMk_mul]⟩
          show ((a * c : φ.ker) : FreeGroup (Fin d)) ∈ H
          rw [Subgroup.coe_mul]
          exact H.mul_mem ha hc
        smul_mem' := by
          rintro c x ⟨a, ha, rfl⟩
          refine ⟨a ^ c.val, ?_, ?_⟩
          · show ((a ^ c.val : φ.ker) : FreeGroup (Fin d)) ∈ H
            rw [Subgroup.coe_pow]
            exact H.pow_mem ha _
          · rw [relVsMk_pow]
            rw [← Nat.cast_smul_eq_nsmul (ZMod p) c.val, ZMod.natCast_zmod_val] }
    have hPtop : P = ⊤ := by
      rw [eq_top_iff, ← b.span_eq]
      refine Submodule.span_le.mpr ?_
      rintro x ⟨i, rfl⟩
      exact ⟨f i,
        (le_sup_left : Subgroup.normalClosure
          (Set.range fun i => ((f i : φ.ker) : FreeGroup (Fin d))) ≤ H)
          (Subgroup.subset_normalClosure (Set.mem_range_self i)),
        hf i⟩
    have hrP : relVsMk p φ.ker ⟨r, hr⟩ ∈ P := by rw [hPtop]; exact Submodule.mem_top
    obtain ⟨h, hhH, hhV⟩ := hrP
    -- `h` and `r` have the same image in `V`, so `h * r⁻¹ ∈ relFt p R ≤ H`
    have hk : (((h * ⟨r, hr⟩⁻¹ : φ.ker)) : FreeGroup (Fin d)) ∈ relFt p φ.ker := by
      apply (relVsMk_eq_zero_iff p φ.ker _).mp
      rw [relVsMk_mul, relVsMk_inv, hhV, add_neg_cancel]
    have hkH : (((h * ⟨r, hr⟩⁻¹ : φ.ker)) : FreeGroup (Fin d)) ∈ H :=
      (le_sup_right : relFt p φ.ker ≤ H) hk
    have hcoe : ((((h * ⟨r, hr⟩⁻¹ : φ.ker))⁻¹ * h : φ.ker) : FreeGroup (Fin d)) = r := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [← hcoe]
    exact H.mul_mem (H.inv_mem hkH) hhH

end Work.Tower.ProPEndgame
