import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.Fund.Pullback
import Submission.Work.KT.Bott.patch_idem_dim

/-!
# `Work.KT.ExtGen.disc_square` — the clutching construction over `C(X × S², ℂ)`

The two-disc decomposition `S² = D₊ ∪_{S¹} D₋` identifies

`C(X × S², ℂ) ≅ pullAlg2 X = {(f₊, f₋) ∈ C(X × D, ℂ)² | f₊| = f₋|}`

(`Work.KT.Fund.Pullback.glueEquiv`).  This is a Cartesian (Milnor) square of rings, and this file
supplies the data that the Milnor machinery of `Submission.Work.KT.Bott` needs in order to run in
that square:

* `bdryRestrict_surjective` — **Tietze**: every continuous function on the boundary circle
  `X × S¹` extends to the disc `X × D`, i.e. restriction to the circle is surjective.  This is the
  hypothesis `hs` of `Work.KT.Bott.patch_idem_dim` (equivalently the "units lift" hypothesis
  `hlift` of `Work.KT.Bott.mvN_glue`, via `Work.KT.Bott.mat_lift_surj`).
* `fstProj`, `sndProj`, `square_comm`, `square_patch` — the two projections out of `pullAlg2 X` and
  the two Cartesian-square properties (`hcomm`, `hpb`).
* `exists_clutching_idem`, `exists_clutching` — **the clutching construction**: for every
  invertible matrix `u` over `C(X × S¹, ℂ)` (a "clutching function") Milnor patching of the two
  trivial bundles along `u` produces an idempotent `Ê` over `pullAlg2 X` whose two disc
  restrictions are the trivial classes.  Its class `κ(u) = [Ê] - [1]` is the element of
  `K̃(C(X × S², ℂ))` of Hatcher's elementary proof of Bott periodicity (Hatcher, *Vector Bundles
  and K-Theory*, Theorem 2.2, step 1; the "clutching" step of
  `Submission/Work/KT/fund_product.lean`).

This is the first layer of the node `Work.KT.fund_product`; it is independent of its later layers
(Laurent approximation, linearisation and the splitting), which live in `Fund/` and `Bott/`.
-/

namespace Work.KT.ExtGen

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The identity matrix is idempotent (a local copy: the workspace contains a second, clashing
`Work.KT.Mat.one_isIdem` whose visibility depends on the import order, cf.
`Submission/Work/KT/NOTES_susp_bijective_status.md`). -/
lemma one_isIdem_D {R : Type} [Ring R] (n : ℕ) : (Mat.one R n).IsIdem := by
  unfold Mat.IsIdem Mat.one
  exact Matrix.one_mul (1 : Matrix (Fin n) (Fin n) R)

/-- The identity matrix is mapped to the identity matrix by a ring homomorphism. -/
lemma Mat_map_one_D {A B : Type} [Ring A] [Ring B] (φ : A →+* B) (n : ℕ) :
    (Mat.one A n).map φ = Mat.one B n := by
  unfold Mat.one Mat.map
  refine Sigma.ext rfl ?_
  refine heq_of_eq ?_
  ext i j
  simp [Matrix.map_apply, Matrix.one_apply]

/-! ## Tietze: restriction to the boundary circle is surjective -/

/-- **Tietze.** Every continuous function on the boundary circle `X × S¹` extends to the closed
disc `X × D`; equivalently `Work.KT.Fund.bdryRestrict X` is surjective. -/
theorem bdryRestrict_surjective : Function.Surjective (Fund.bdryRestrict X) := by
  intro g
  -- the boundary circle, as a closed subset of the disc
  have hS : IsClosed {q : X × Ball ℂ | ‖(q.2 : ℂ)‖ = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  -- `g` viewed as a function on that closed subset
  let ψ : C(↥{q : X × Ball ℂ | ‖(q.2 : ℂ)‖ = 1}, ℂ) :=
    ⟨fun p => g (p.1.1, ⟨(p.1.2 : ℂ), by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
        exact p.2⟩),
      by fun_prop⟩
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq hS ψ
  refine ⟨F, ?_⟩
  ext p
  have hp : ((p.1, Fund.sphIncl p.2) : X × Ball ℂ) ∈
      {q : X × Ball ℂ | ‖(q.2 : ℂ)‖ = 1} := by
    show ‖((Fund.sphIncl p.2 : Ball ℂ) : ℂ)‖ = 1
    exact Fund.norm_coe_sph p.2
  have h2 : F (p.1, Fund.sphIncl p.2) =
      ψ ⟨(p.1, Fund.sphIncl p.2), hp⟩ := by
    have h := congrFun
      (congrArg (fun m : C(↥{q : X × Ball ℂ | ‖(q.2 : ℂ)‖ = 1}, ℂ) => (m : _ → ℂ)) hF)
      ⟨(p.1, Fund.sphIncl p.2), hp⟩
    simpa using h
  rw [Fund.bdryRestrict_apply, h2]
  exact congrArg g (Prod.ext rfl (Subtype.ext rfl))

/-! ## The two projections out of the fibre product -/

/-- The first projection `pullAlg2 X → C(X × D, ℂ)` (the upper disc). -/
def fstProj : ↥(Fund.pullAlg2 X) →+* C(X × Ball ℂ, ℂ) :=
  (RingHom.fst (C(X × Ball ℂ, ℂ)) (C(X × Ball ℂ, ℂ))).comp
    (Fund.pullAlg2 X).val.toRingHom

/-- The second projection `pullAlg2 X → C(X × D, ℂ)` (the lower disc). -/
def sndProj : ↥(Fund.pullAlg2 X) →+* C(X × Ball ℂ, ℂ) :=
  (RingHom.snd (C(X × Ball ℂ, ℂ)) (C(X × Ball ℂ, ℂ))).comp
    (Fund.pullAlg2 X).val.toRingHom

@[simp] lemma fstProj_apply (z : ↥(Fund.pullAlg2 X)) : fstProj X z = z.1.1 := rfl

@[simp] lemma sndProj_apply (z : ↥(Fund.pullAlg2 X)) : sndProj X z = z.1.2 := rfl

/-- Membership in the fibre product, by definition. -/
lemma mem_pullAlg2_iff (z : C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ)) :
    z ∈ Fund.pullAlg2 X ↔ Fund.bdryRestrict X z.1 = Fund.bdryRestrict X z.2 :=
  Iff.rfl

/-- The square `pullAlg2 X → C(X × D, ℂ) → C(X × S¹, ℂ)` commutes (`hcomm`). -/
lemma square_comm :
    (Fund.bdryRestrict X).comp (fstProj X) = (Fund.bdryRestrict X).comp (sndProj X) := by
  ext z a
  have hz : Fund.bdryRestrict X (z : C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ)).1
      = Fund.bdryRestrict X (z : C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ)).2 :=
    (mem_pullAlg2_iff X (z : C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ))).mp z.2
  simpa using congrArg (fun m : C(X × Sph ℂ, ℂ) => m a) hz

/-- The square is Cartesian (`hpb`): a pair of disc functions with the same boundary values is the
pair of restrictions of a unique element of `pullAlg2 X`. -/
lemma square_patch (x₁ x₂ : C(X × Ball ℂ, ℂ))
    (h : Fund.bdryRestrict X x₁ = Fund.bdryRestrict X x₂) :
    ∃! z : ↥(Fund.pullAlg2 X), fstProj X z = x₁ ∧ sndProj X z = x₂ := by
  refine ⟨⟨(x₁, x₂), h⟩, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨⟨y₁, y₂⟩, hy⟩ ⟨e₁, e₂⟩
  exact Subtype.ext (Prod.ext e₁ e₂)

/-! ## The clutching construction -/

/-- **The clutching construction** (Hatcher, VBKT Theorem 2.2, step 1).  Milnor patching of the
two trivial rank-`n` bundles over the two discs along an invertible matrix `u` over the common
boundary circle produces an idempotent matrix `Ê` over the disc-square algebra `pullAlg2 X` whose
two disc restrictions are the identity classes. -/
theorem exists_clutching_idem (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    ∃ Ê : Mat ↥(Fund.pullAlg2 X), Ê.IsIdem ∧
      cls (Ê.map (fstProj X)) = cls (Mat.one (C(X × Ball ℂ, ℂ)) n) ∧
      cls (Ê.map (sndProj X)) = cls (Mat.one (C(X × Ball ℂ, ℂ)) n) := by
  have hone : (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map (Fund.bdryRestrict X) =
      (1 : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    simp
  -- the patching data, as matrices over the boundary circle
  set S : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) := ↑u with hS
  set T : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ) := ↑(u⁻¹) with hT
  have hST : S * T = (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map (Fund.bdryRestrict X) := by
    have h : S * T = 1 := by rw [hS, hT]; simp
    rw [h, hone.symm]
  have hTS : T * S = (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map (Fund.bdryRestrict X) := by
    have h : T * S = 1 := by rw [hS, hT]; simp
    rw [h, hone.symm]
  exact Bott.patch_idem_dim (fstProj X) (sndProj X) (Fund.bdryRestrict X) (Fund.bdryRestrict X)
    (bdryRestrict_surjective X) (square_comm X) (square_patch X)
    (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (by simp) (by simp) S T hST hTS

/-- **The clutched class.**  The class `κ(u) = [Ê] - [1]` of the previous theorem is reduced: it
restricts to `0` on each of the two discs, i.e. it lies in `K̃(C(X × S², ℂ))` realised inside
`K0 (pullAlg2 X)`. -/
theorem exists_clutching (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    ∃ z : K0 ↥(Fund.pullAlg2 X), K0.map (fstProj X) z = 0 ∧ K0.map (sndProj X) z = 0 := by
  obtain ⟨Ê, hÊ, h1, h2⟩ := exists_clutching_idem X n u
  refine ⟨cls Ê - cls (Mat.one ↥(Fund.pullAlg2 X) n), ?_, ?_⟩
  · rw [map_sub, K0.map_cls (fstProj X) hÊ, h1, K0.map_cls (fstProj X) (one_isIdem_D n),
      Mat_map_one_D (fstProj X) n, sub_self]
  · rw [map_sub, K0.map_cls (sndProj X) hÊ, h2, K0.map_cls (sndProj X) (one_isIdem_D n),
      Mat_map_one_D (sndProj X) n, sub_self]

/-! ## The clutched class on `C(X × S², ℂ)` -/

/-- `fstProj` intertwines `pullUp` with the identification `glueEquiv`. -/
lemma fstProj_glueEquiv (g : C(X × S2, ℂ)) :
    fstProj X (Fund.glueEquiv X g) = Fund.pullUp X g := by
  simp [fstProj_apply, Fund.glueEquiv_apply]

/-- The same, in the form used below: `pullUp X ∘ (glueEquiv X).symm = fstProj X`. -/
lemma fstProj_comp_glueEquiv_symm :
    (Fund.pullUp X).comp ((Fund.glueEquiv X).symm.toRingHom) = fstProj X := by
  ext z a
  have h := fstProj_glueEquiv X ((Fund.glueEquiv X).symm z)
  rw [AlgEquiv.apply_symm_apply] at h
  simpa using congrArg (fun m : C(X × Ball ℂ, ℂ) => m a) h.symm

/-- `sndProj` intertwines `pullDn` with the identification `glueEquiv`. -/
lemma sndProj_glueEquiv (g : C(X × S2, ℂ)) :
    sndProj X (Fund.glueEquiv X g) = Fund.pullDn X g := by
  simp [sndProj_apply, Fund.glueEquiv_apply]

/-- The same, in the form used below: `pullDn X ∘ (glueEquiv X).symm = sndProj X`. -/
lemma sndProj_comp_glueEquiv_symm :
    (Fund.pullDn X).comp ((Fund.glueEquiv X).symm.toRingHom) = sndProj X := by
  ext z a
  have h := sndProj_glueEquiv X ((Fund.glueEquiv X).symm z)
  rw [AlgEquiv.apply_symm_apply] at h
  simpa using congrArg (fun m : C(X × Ball ℂ, ℂ) => m a) h.symm

/-- **The clutched class in `K0 (C(X × S², ℂ))`**, i.e. the form in which the assembly of
`Work.KT.fund_product` uses it: a class whose two disc restrictions vanish. -/
theorem exists_clutching_sphere (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    ∃ z : K0 C(X × S2, ℂ),
      K0.map (Fund.pullUp X) z = 0 ∧ K0.map (Fund.pullDn X) z = 0 := by
  obtain ⟨z₀, hz₀₁, hz₀₂⟩ := exists_clutching X n u
  refine ⟨K0.map ((Fund.glueEquiv X).symm.toRingHom) z₀, ?_, ?_⟩
  · rw [← K0.map_comp_apply (Fund.glueEquiv X).symm.toRingHom (Fund.pullUp X) z₀,
      fstProj_comp_glueEquiv_symm X]
    exact hz₀₁
  · rw [← K0.map_comp_apply (Fund.glueEquiv X).symm.toRingHom (Fund.pullDn X) z₀,
      sndProj_comp_glueEquiv_symm X]
    exact hz₀₂

/-- **`κ(1) = 0`**: the trivial clutching function gives the trivial class.  (The patched
idempotent is `Mat.one`, which is idempotent and restricts to the identity classes.) -/
theorem exists_clutching_idem_one (n : ℕ) :
    ∃ Ê : Mat ↥(Fund.pullAlg2 X), Ê.IsIdem ∧
      cls (Ê.map (fstProj X)) = cls (Mat.one (C(X × Ball ℂ, ℂ)) n) ∧
      cls (Ê.map (sndProj X)) = cls (Mat.one (C(X × Ball ℂ, ℂ)) n) ∧
      Ê = Mat.one ↥(Fund.pullAlg2 X) n :=
  ⟨Mat.one ↥(Fund.pullAlg2 X) n, one_isIdem_D n,
    by rw [Mat_map_one_D (fstProj X) n],
    by rw [Mat_map_one_D (sndProj X) n], rfl⟩

end

end Work.KT.ExtGen
