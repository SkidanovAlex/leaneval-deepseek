import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.Shafarevich.Defs
import Submission.Work.GolodShafarevich.Defs
import Submission.Work.GolodShafarevich.Setup
import Submission.Work.GolodShafarevich.Assembly
import Submission.Work.GolodShafarevich.AbstractGS.gs_dimension_bound
import Submission.Work.GolodShafarevich.RelationModule.ker_psi_eq_span

/-!
# The pro-`p` Golod–Šafarevič endgame: vocabulary

This file fixes the vocabulary for the pro-`p` Golod–Šafarevič inequality for finite `p`-groups
in the form used by the tower endgame: a nontrivial finite `p`-group `G` with a minimal
presentation `φ : F_d ↠ G` satisfies `4 · dim_{𝔽_p} H²(G, 𝔽_p) > d²`.

The proof goes through the **pro-`p` relation module** `N = ker ψ ⊆ 𝔽_p[G]^d` (`ψ` from
`Work.GolodShafarevich`), which is generated as an `𝔽_p[G]`-module by the Fox derivative vectors of
any set of elements of `R = ker φ` whose images generate the `𝔽_p`-vector space
`V = R / ([R,R]·[R,F]·R^p)` (here `relFt p R = [R,F]·R^p` and the commutator subgroup `[R,R]` is
divided out by passing to the abelianization of `R`).  The dimension `dim_{𝔽_p} V` is the pro-`p`
relation rank of `G` (it equals `dim_{𝔽_p} H²(G, 𝔽_p)`), and it is the number that the
Golod–Šafarevič dimension argument consumes.

## Main definitions

* `Work.Tower.ProPEndgame.relFt p R` — the subgroup `[R,F]·R^p ≤ F` of a subgroup `R ≤ F`.
* `Work.Tower.ProPEndgame.relVs p R` — the `𝔽_p`-vector space `R / relFt p R`.
* `Work.Tower.ProPEndgame.relVsMk p R` — the canonical map `R → relVs p R`.
* `Work.Tower.ProPEndgame.relRank p R` — `dim_{𝔽_p} (R / relFt p R)`, the pro-`p` relation rank
  of the presentation.
-/

open scoped Classical
open scoped MonoidAlgebra
open scoped commutatorElement

namespace Work.Tower.ProPEndgame

/-! ## The relation-Frattini subgroup `[R,F]·R^p` -/

/-- For a subgroup `R ≤ F` and a natural number `p`, the subgroup `[R,F]·R^p` of `F`, defined as
the normal closure of the commutators of an element of `R` with an element of `F` (written as
`f * r * f⁻¹ * r⁻¹`) and the `p`-th powers of elements of `R`.  Together with the commutator
subgroup (which is divided out by the abelianization) this is the subgroup whose quotient is the
`𝔽_p`-vector space of "relations modulo the `p`-th powers". -/
def relFt (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) : Subgroup F :=
  Subgroup.normalClosure
    ((Set.range fun x : R × F => x.2 * (x.1 : F) * x.2⁻¹ * (x.1 : F)⁻¹)
      ∪ (Set.range fun x : R => (x.1 : F) ^ p))

/-- The generators of `relFt` all lie in `R`. -/
theorem relFt_le (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) (hR : R.Normal) :
    relFt p R ≤ R := by
  haveI : R.Normal := hR
  refine Subgroup.normalClosure_le_normal ?_
  rintro x (hx | hx)
  · obtain ⟨y, rfl⟩ := hx
    have h1 : y.2 * (y.1 : F) * y.2⁻¹ ∈ R := Subgroup.Normal.conj_mem hR (y.1 : F) y.1.2 y.2
    exact R.mul_mem h1 (R.inv_mem y.1.2)
  · obtain ⟨y, rfl⟩ := hx
    exact R.pow_mem y.2 p

/-- The commutator generators lie in `relFt`. -/
theorem relFt_conj_mem (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) (r : R) (f : F) :
    f * (r : F) * f⁻¹ * (r : F)⁻¹ ∈ relFt p R :=
  Subgroup.subset_normalClosure (Or.inl ⟨(r, f), rfl⟩)

/-- The `p`-th power generators lie in `relFt`. -/
theorem relFt_pow_mem (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) (r : R) :
    (r : F) ^ p ∈ relFt p R :=
  Subgroup.subset_normalClosure (Or.inr ⟨r, rfl⟩)

/-- The commutator subgroup of `R` is contained in `relFt`. -/
theorem commutator_le_relFt (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) :
    Subgroup.map R.subtype (_root_.commutator R) ≤ relFt p R := by
  rw [Subgroup.map_le_iff_le_comap, commutator_eq_closure, Subgroup.closure_le]
  rintro x ⟨r, s, rfl⟩
  show ((r * s * r⁻¹ * s⁻¹ : R) : F) ∈ relFt p R
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using relFt_conj_mem p R s r

/-! ## The `𝔽_p`-vector space `R / ([R,R]·[R,F]·R^p)` -/

/-- The image of `relFt p R` in the abelianization of `R`, as an additive subgroup. -/
noncomputable def relFtSub (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) :
    AddSubgroup (Additive (Abelianization R)) :=
  (Subgroup.map (Abelianization.of (G := R)) ((relFt p R).subgroupOf R)).toAddSubgroup

/-- The `𝔽_p`-vector space `V = R / ([R,R]·[R,F]·R^p)`. -/
noncomputable abbrev relVs (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) : Type _ :=
  (Additive (Abelianization R)) ⧸ relFtSub p R

/-- The canonical map `R → relVs p R`. -/
noncomputable def relVsMk (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) (r : R) :
    relVs p R :=
  QuotientAddGroup.mk (Additive.ofMul (Abelianization.of (G := R) r))

/-- `relVsMk` is additive on `R`. -/
theorem relVsMk_mul (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) (r s : R) :
    relVsMk p R (r * s) = relVsMk p R r + relVsMk p R s := by
  show QuotientAddGroup.mk (Additive.ofMul (Abelianization.of (r * s))) = _
  rw [map_mul]
  rfl

/-- `relVsMk` is surjective. -/
theorem relVsMk_surjective (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) :
    Function.Surjective (relVsMk p R) := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ y =>
    obtain ⟨r, hr⟩ : ∃ r : R, Additive.ofMul (Abelianization.of (G := R) r) = y := by
      obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective (s := _root_.commutator R) (Additive.toMul y)
      refine ⟨r, ?_⟩
      show Additive.ofMul (QuotientGroup.mk r) = y
      rw [hr]
      rfl
    refine ⟨r, ?_⟩
    show QuotientAddGroup.mk (Additive.ofMul (Abelianization.of r)) = QuotientAddGroup.mk y
    rw [hr]

/-- If `r ∈ relFt p R` then `relVsMk` kills `r`. -/
theorem relVsMk_eq_zero_of_mem (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) (r : R)
    (h : (r : F) ∈ relFt p R) : relVsMk p R r = 0 := by
  rw [relVsMk, QuotientAddGroup.eq_zero_iff, relFtSub, Additive.mem_toAddSubgroup,
    Subgroup.mem_map]
  exact ⟨r, (Subgroup.mem_subgroupOf (H := relFt p R) (K := R)).mpr h, rfl⟩

/-- If `r * s⁻¹ ∈ relFt p R` then `relVsMk` identifies `r` and `s`. -/
theorem relVsMk_eq_of_mem (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) (r s : R)
    (h : (r * s⁻¹ : R) ∈ (relFt p R).subgroupOf R) : relVsMk p R r = relVsMk p R s := by
  have h' : ((r * s⁻¹ : R) : F) ∈ relFt p R :=
    (Subgroup.mem_subgroupOf (H := relFt p R) (K := R)).mp h
  have h2 : relVsMk p R (r * s⁻¹) = 0 := relVsMk_eq_zero_of_mem p R _ h'
  have hrs : r = (r * s⁻¹) * s := by group
  calc relVsMk p R r = relVsMk p R ((r * s⁻¹) * s) := congrArg (relVsMk p R) hrs
    _ = relVsMk p R (r * s⁻¹) + relVsMk p R s := relVsMk_mul p R _ _
    _ = relVsMk p R s := by rw [h2, zero_add]

/-- `relVsMk` kills conjugation by elements of `F`. -/
theorem relVsMk_conj (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) (hR : R.Normal)
    (r : R) (f : F) :
    relVsMk p R ⟨f * (r : F) * f⁻¹, hR.conj_mem _ r.2 f⟩ = relVsMk p R r := by
  refine relVsMk_eq_of_mem p R _ r ?_
  show ((f * (r : F) * f⁻¹) * (r : F)⁻¹ : F) ∈ relFt p R
  simpa [mul_assoc] using relFt_conj_mem p R r f

/-- `relVsMk r = 0` iff `r` lies in `[R,R]·[R,F]·R^p`. -/
theorem relVsMk_eq_zero_iff (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) (r : R) :
    relVsMk p R r = 0 ↔ (r : F) ∈ relFt p R := by
  constructor
  · intro h
    have h' : Additive.ofMul (Abelianization.of (G := R) r) ∈ relFtSub p R := by
      have h2 := h
      rw [relVsMk] at h2
      exact (QuotientAddGroup.eq_zero_iff _).mp h2
    rw [relFtSub, Additive.mem_toAddSubgroup, toMul_ofMul] at h'
    obtain ⟨m, hm, hmr⟩ := Subgroup.mem_map.mp h'
    have hm' : (m : F) ∈ relFt p R := (Subgroup.mem_subgroupOf (H := relFt p R) (K := R)).mp hm
    have hker : (r * m⁻¹ : R) ∈ _root_.commutator R := by
      have h2 : Abelianization.of (G := R) (r * m⁻¹) = 1 := by
        rw [map_mul, map_inv, hmr.symm, mul_inv_cancel]
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]
      exact h2
    have h3 : ((r * m⁻¹ : R) : F) ∈ relFt p R :=
      commutator_le_relFt p R (Subgroup.mem_map.mpr ⟨(r * m⁻¹ : R), hker, rfl⟩)
    have h4 : (r : F) = ((r * m⁻¹ : R) : F) * (m : F) := by simp
    rw [h4]
    exact Subgroup.mul_mem _ h3 hm'
  · exact relVsMk_eq_zero_of_mem p R r

/-- `relVsMk (r ^ n) = n • relVsMk r`. -/
theorem relVsMk_pow (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) (r : R) (n : ℕ) :
    relVsMk p R (r ^ n) = n • relVsMk p R r := by
  induction n with
  | zero => simp [relVsMk]
  | succ n ih => rw [pow_succ, relVsMk_mul, ih, succ_nsmul]

/-- The normal form of `n • x` in the additive group `Additive G`. -/
theorem nsmul_ofMul {G : Type*} [Group G] (n : ℕ) (g : G) :
    n • (Additive.ofMul g) = Additive.ofMul (g ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, ih, pow_succ]; rfl

/-- `relVs p R` carries a natural `𝔽_p`-module structure. -/
noncomputable instance relVsModule (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) :
    Module (ZMod p) (relVs p R) :=
  QuotientAddGroup.zmodModule (H := relFtSub p R) (n := p) (fun x => by
    obtain ⟨r, hr⟩ : ∃ r : R, Additive.ofMul (Abelianization.of (G := R) r) = x := by
      obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective (s := _root_.commutator R) (Additive.toMul x)
      refine ⟨r, ?_⟩
      show Additive.ofMul (QuotientGroup.mk r) = x
      rw [hr]
      rfl
    rw [← hr, nsmul_ofMul]
    refine Additive.mem_toAddSubgroup _ _ |>.mpr ?_
    refine Subgroup.mem_map.mpr ⟨r ^ p, ?_, ?_⟩
    · exact (Subgroup.mem_subgroupOf (H := relFt p R) (K := R)).mpr (by
        show ((r ^ p : R) : F) ∈ relFt p R
        push_cast
        exact relFt_pow_mem p R r)
    · rw [map_pow]
      rfl)

/-- The pro-`p` relation rank `dim_{𝔽_p} (R/([R,R]·[R,F]·R^p))` of a presentation `R ≤ F`. -/
noncomputable def relRank (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) : ℕ :=
  Module.finrank (ZMod p) (relVs p R)

end Work.Tower.ProPEndgame
