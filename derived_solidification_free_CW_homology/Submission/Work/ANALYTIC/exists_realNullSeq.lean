import Mathlib
import Submission.Work.ANALYTIC.RealCond
import Submission.Work.ANALYTIC.nullSeqDefs
import Submission.Work.ATOM.projective_P
import Submission.Work.DISC.homFreeEquiv_naturality

/-!
# The parametrised null sequence of REFS/03 §3

Helper lemmas for `Work.ANALYTIC.exists_realNullSeq`: the parametrised null sequence
`e_n ↦ r * (1/2)^(log₂(n+1))` on `P = ℤ[ℕ∪∞]/ℤ[∞]`, together with the companion endomorphisms
`F : e_n ↦ e_{2n+1} + e_{2n+2}` and `G : e_n ↦ e_{2n+1}` and the points `e₀`, `e₁` of `P`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-! ## Sections of `realCond`

The `S`-points of `realCond` are definitionally the continuous functions `S → ℝ`
(`realCond_obj_obj`), but the elaborator does not see the coercion to a function; the two identity
maps below make the coercion explicit. -/

/-- The identity coercion from continuous functions to sections of `realCond`. -/
def sec {S : LightProfinite} (v : C(S, ℝ)) : ↥(realCond.obj.obj (op S)) := v

/-- The identity coercion from sections of `realCond` to continuous functions. -/
def secInv {S : LightProfinite} (v : ↥(realCond.obj.obj (op S))) : C(S, ℝ) := v

@[simp]
theorem secInv_sec {S : LightProfinite} (v : C(S, ℝ)) : secInv (sec v) = v := rfl

@[simp]
theorem sec_secInv {S : LightProfinite} (v : ↥(realCond.obj.obj (op S))) : sec (secInv v) = v := rfl

/-- Evaluation of a continuous function on a light profinite set at a point. -/
def ev {S : LightProfinite} (v : C(S, ℝ)) (x : ↥S.toTop) : ℝ := v x

theorem ev_sec {S : LightProfinite} (v : C(S, ℝ)) (x : ↥S.toTop) :
    ev (secInv (sec v)) x = ev v x := rfl

/-- The constant function with value `r`. -/
def constC (S : LightProfinite) (r : ℝ) : C(S, ℝ) := ⟨fun _ => r, continuous_const⟩

@[simp]
theorem constC_apply (S : LightProfinite) (r : ℝ) (x : ↥S.toTop) : constC S r x = r := rfl

/-- The action of `realCond` on morphisms is precomposition. -/
theorem realCond_map_comp {S T : LightProfinite} (f : T ⟶ S) (g : C(S, ℝ)) :
    (realCond.obj.map f.op g : C(T, ℝ)) = g.comp (LightProfinite.toTopCat.map f).hom := rfl

theorem realCond_map_apply {S T : LightProfinite} (f : T ⟶ S) (g : C(S, ℝ)) (x : ↥T.toTop) :
    (g.comp (LightProfinite.toTopCat.map f).hom : C(T, ℝ)) x = g (f x) := rfl

theorem ev_map {S T : LightProfinite} (f : T ⟶ S) (g : C(S, ℝ)) (x : ↥T.toTop) :
    ev (secInv (realCond.obj.map f.op (sec g))) x = ev g (f x) := by
  rw [show secInv (realCond.obj.map f.op (sec g)) =
    g.comp (LightProfinite.toTopCat.map f).hom from rfl]
  exact realCond_map_apply f g x

/-- Two sections of `realCond` which agree at every point are equal. -/
theorem realCond_ext {S : LightProfinite} {v w : ↥(realCond.obj.obj (op S))}
    (h : ∀ x : ↥S.toTop, ev (secInv v) x = ev (secInv w) x) : v = w := by
  show (secInv v : C(S, ℝ)) = (secInv w : C(S, ℝ))
  exact ContinuousMap.ext h

theorem realCond_map_zero {S T : LightProfinite} (f : T ⟶ S) (g : C(S, ℝ))
    (h : ∀ x : ↥T.toTop, g (f x) = 0) : realCond.obj.map f.op (sec g) = 0 := by
  apply realCond_ext
  intro x
  rw [ev_map]
  show g (f x) = 0
  exact h x

/-! ## The comparison `Hom(ℤ[S], M) ≃ M(S)` -/

/-- The section of the free object corresponding to the identity, used to express the comparison
`Hom(ℤ[S], M) ≃ M(S)` as an evaluation. -/
def secUnit (S : LightProfinite) : ↥(((free ℤ).obj S.toCondensed).obj.obj (op S)) :=
  (coherentTopology LightProfinite).yonedaEquiv
    ((LightCondensed.freeForgetAdjunction ℤ).unit.app S.toCondensed)

theorem freeHomEquiv_eq (S : LightProfinite) (M : LightCondAb)
    (g : (free ℤ).obj S.toCondensed ⟶ M) :
    freeHomEquiv S M g = g.hom.app (op S) (secUnit S) := by
  show (coherentTopology LightProfinite).yonedaEquiv
      ((LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed M g) = _
  rw [Adjunction.homEquiv_apply]
  refine (GrothendieckTopology.yonedaEquiv_comp (coherentTopology LightProfinite) _
    ((LightCondensed.forget ℤ).map g)).trans ?_
  exact LightCondensed.forget_map_hom_app_hom_apply ℤ g (op S) _

theorem moduleCat_hom_add_apply {M N : ModuleCat ℤ} (f g : M ⟶ N) (x : M) :
    ConcreteCategory.hom (f + g) x = ConcreteCategory.hom f x + ConcreteCategory.hom g x := by
  show (f + g).hom' x = f.hom' x + g.hom' x
  exact LinearMap.add_apply _ _ _

/-- The comparison `Hom(ℤ[S], M) ≃ M(S)` is additive. -/
theorem freeHomEquiv_add (S : LightProfinite) (M : LightCondAb)
    (a b : (free ℤ).obj S.toCondensed ⟶ M) :
    freeHomEquiv S M (a + b) = freeHomEquiv S M a + freeHomEquiv S M b := by
  rw [freeHomEquiv_eq S M (a + b), freeHomEquiv_eq S M a, freeHomEquiv_eq S M b]
  rw [Sheaf.Hom.add_app]
  exact moduleCat_hom_add_apply _ _ (secUnit S)

theorem freeHomEquiv_zero (S : LightProfinite) (M : LightCondAb) :
    freeHomEquiv S M 0 = 0 := by
  have h := freeHomEquiv_add S M 0 0
  rw [zero_add] at h
  exact add_left_cancel (a := freeHomEquiv S M 0) (by rw [← h, add_zero])

/-- Naturality of `Hom(ℤ[S], M) ≃ M(S)` in `S`. -/
theorem freeHomEquiv_naturality {S T : LightProfinite} (f : T ⟶ S) (M : LightCondAb)
    (g : (free ℤ).obj S.toCondensed ⟶ M) :
    freeHomEquiv T M ((lightProfiniteToLightCondSet ⋙ free ℤ).map f ≫ g) =
      M.obj.map f.op (freeHomEquiv S M g) :=
  Work.DISC.homFreeEquiv_naturality T S f M g

/-- Naturality of `Hom(ℤ[S], M) ≃ M(S)` in `M`. -/
theorem freeHomEquiv_naturality_target (S : LightProfinite) {M N : LightCondAb} (φ : M ⟶ N)
    (g : (free ℤ).obj S.toCondensed ⟶ M) :
    freeHomEquiv S N (g ≫ φ) = φ.hom.app (op S) (freeHomEquiv S M g) :=
  Work.ATOM.homFreeEquiv_naturality_target S φ g

/-! ## The free functor on light profinite sets -/

/-- `S ↦ ℤ[S]`, the free light condensed abelian group on a light profinite set. -/
abbrev zf : LightProfinite.{0} ⥤ LightCondAb := lightProfiniteToLightCondSet ⋙ free ℤ

/-! ## `P = ℤ[ℕ∪∞]/ℤ[∞]` -/

theorem P_proj_P_homMk {A : LightCondAb} (φ : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ A)
    (h : P_map ≫ φ = 0) : P_proj ≫ P_homMk A φ h = φ :=
  cokernel.π_desc _ _ _

theorem P_proj_oneMinusShift :
    P_proj ≫ oneMinusShift = oneMinusShift' ≫ P_proj := by
  rw [LightCondensed.oneMinusShift, ← Category.assoc, P_proj_P_homMk]

/-- Precomposition with `P_proj` is injective (it is split by the retraction `P_retract.i`). -/
theorem P_cancel {Z : LightCondAb} {a b : P ⟶ Z} (h : P_proj ≫ a = P_proj ≫ b) : a = b := by
  have hs : P_retract.i ≫ P_proj = 𝟙 P := P_retract.retract
  calc a = (P_retract.i ≫ P_proj) ≫ a := by rw [hs, Category.id_comp]
    _ = P_retract.i ≫ (P_proj ≫ a) := by rw [Category.assoc]
    _ = P_retract.i ≫ (P_proj ≫ b) := by rw [h]
    _ = (P_retract.i ≫ P_proj) ≫ b := by rw [Category.assoc]
    _ = b := by rw [hs, Category.id_comp]

/-- The map `ι : ∗ ⟶ ℕ∪{∞}` (the point at infinity) followed by any map fixing `∞` is `ι`. -/
theorem iota_comp {φ : ℕ∪{∞} ⟶ ℕ∪{∞}} (h : φ ∞ = ∞) :
    LightCondensed.ι ≫ φ = LightCondensed.ι := by
  apply ConcreteCategory.hom_ext
  intro x
  show φ (LightCondensed.ι x) = LightCondensed.ι x
  rw [show LightCondensed.ι x = ∞ from rfl, h]

/-! ## The identities at the level of the free object `ℤ[ℕ∪∞]` -/

theorem zf_phiA_shift : zf.map phiA ≫ zf.map LightProfinite.shift = zf.map phiB := by
  rw [← Functor.map_comp, phiA_shift]

theorem zf_phiB_shift :
    zf.map phiB ≫ zf.map LightProfinite.shift = zf.map (LightProfinite.shift ≫ phiA) := by
  rw [← Functor.map_comp, phiB_shift]

/-- The arithmetic identity underlying `f(F(e_n)) = f(e_n)`: the two children `2n+1` and `2n+2`
of `n` are one level deeper than `n`, so `lam r (2n+1) = lam r (2n+2) = lam r n / 2`. -/
theorem lam_arith (r : ℝ) (n : ℕ) :
    r * (1 / 2) ^ (Nat.log2 (2 * n + 2)) + r * (1 / 2) ^ (Nat.log2 (2 * n + 3))
      = r * (1 / 2) ^ (Nat.log2 (n + 1)) := by
  have hpow : 2 ^ Nat.log2 (n + 1) ≤ n + 1 := (Nat.le_log2 (by omega)).mp le_rfl
  have hlt : n + 1 < 2 ^ (Nat.log2 (n + 1) + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n + 1)
    rw [Nat.log2_eq_log_two]
    simpa [Nat.succ_eq_add_one] using h
  have h1 : Nat.log2 (2 * n + 2) = Nat.log2 (n + 1) + 1 := by
    rw [Nat.log2_eq_iff (by omega)]
    constructor
    · calc 2 ^ (Nat.log2 (n + 1) + 1) = 2 * 2 ^ Nat.log2 (n + 1) := by rw [pow_succ]; ring
        _ ≤ 2 * (n + 1) := Nat.mul_le_mul_left 2 hpow
        _ = 2 * n + 2 := by ring
    · rw [pow_succ]
      omega
  have h2 : Nat.log2 (2 * n + 3) = Nat.log2 (n + 1) + 1 := by
    rw [Nat.log2_eq_iff (by omega)]
    constructor
    · calc 2 ^ (Nat.log2 (n + 1) + 1) = 2 * 2 ^ Nat.log2 (n + 1) := by rw [pow_succ]; ring
        _ ≤ 2 * (n + 1) := Nat.mul_le_mul_left 2 hpow
        _ ≤ 2 * n + 3 := by omega
    · rw [pow_succ]
      omega
  rw [h1, h2]
  have h4 : (1 / 2 : ℝ) ^ Nat.log2 (n + 1) = 2 * (1 / 2) ^ (Nat.log2 (n + 1) + 1) := by
    rw [pow_succ]; ring
  rw [h4]
  ring

/-- The value of the null sequence at the two children of `n`: `lamC r (2n+1) + lamC r (2n+2)`. -/
theorem lamC_children (r : ℝ) (n : ℕ) :
    lamC r (OnePoint.some (2 * n + 1)) + lamC r (OnePoint.some (2 * n + 2)) =
      lamC r (OnePoint.some n) := by
  show lam r (2 * n + 1) + lam r (2 * n + 2) = lam r n
  simp only [lam]
  rw [show 2 * n + 1 + 1 = 2 * n + 2 from by omega,
    show 2 * n + 2 + 1 = 2 * n + 3 from by omega]
  exact lam_arith r n

/-- The identity `F₀ ∘ (1-S) = (1-S) ∘ G₀` at the level of the free object `ℤ[ℕ∪∞]`. -/
theorem F0_oneMinusShift_comm :
    (zf.map phiA + zf.map phiB) ≫ oneMinusShift' = oneMinusShift' ≫ zf.map phiA := by
  have hA := zf_phiA_shift
  have hB := zf_phiB_shift
  calc (zf.map phiA + zf.map phiB) ≫ oneMinusShift'
      = (zf.map phiA + zf.map phiB) ≫ (𝟙 _ - zf.map LightProfinite.shift) := rfl
    _ = (zf.map phiA + zf.map phiB) - (zf.map phiA + zf.map phiB) ≫
          zf.map LightProfinite.shift := by
        rw [Preadditive.comp_sub, Category.comp_id]
    _ = (zf.map phiA + zf.map phiB) - (zf.map phiA ≫ zf.map LightProfinite.shift +
          zf.map phiB ≫ zf.map LightProfinite.shift) := by
        rw [Preadditive.add_comp]
    _ = zf.map phiA - zf.map (LightProfinite.shift ≫ phiA) := by
        rw [hA, hB]; abel
    _ = zf.map phiA - zf.map LightProfinite.shift ≫ zf.map phiA := by
        rw [Functor.map_comp]
    _ = (𝟙 _ - zf.map LightProfinite.shift) ≫ zf.map phiA := by
        rw [Preadditive.sub_comp, Category.id_comp]
    _ = oneMinusShift' ≫ zf.map phiA := rfl

/-- The null sequence `g` satisfies `F₀ ∘ g = g`. -/
theorem F0_comp_g (r : ℝ) :
    (zf.map phiA + zf.map phiB) ≫ (freeHomEquiv (ℕ∪{∞}) realCond).symm (sec (lamC r)) =
      (freeHomEquiv (ℕ∪{∞}) realCond).symm (sec (lamC r)) := by
  apply (freeHomEquiv (ℕ∪{∞}) realCond).injective
  rw [Preadditive.add_comp, freeHomEquiv_add, freeHomEquiv_naturality, freeHomEquiv_naturality,
    Equiv.apply_symm_apply]
  apply realCond_ext
  intro x
  rw [show secInv (realCond.obj.map phiA.op (sec (lamC r)) +
      realCond.obj.map phiB.op (sec (lamC r))) =
      secInv (realCond.obj.map phiA.op (sec (lamC r))) +
      secInv (realCond.obj.map phiB.op (sec (lamC r))) from rfl]
  have hsum : ev (secInv (realCond.obj.map phiA.op (sec (lamC r))) +
      secInv (realCond.obj.map phiB.op (sec (lamC r)))) x =
      ev (secInv (realCond.obj.map phiA.op (sec (lamC r)))) x +
      ev (secInv (realCond.obj.map phiB.op (sec (lamC r)))) x :=
    ContinuousMap.add_apply _ _ x
  rw [hsum, ev_map, ev_map, ev_sec]
  cases x with
  | none =>
      show (0 : ℝ) + 0 = 0
      norm_num
  | some n =>
      show lam r (2 * n + 1) + lam r (2 * n + 2) = lam r n
      simp only [lam]
      rw [show 2 * n + 1 + 1 = 2 * n + 2 from by omega,
        show 2 * n + 2 + 1 = 2 * n + 3 from by omega]
      exact lam_arith r n

end Work.ANALYTIC

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- **The parametrised null sequence of REFS/03 §3 with prescribed value at `e₀`.**  For every
`u : 𝟙_ LightCondAb ⟶ realCond` (morally a real number, the value of the null sequence at `e₀`)
there are `f : P ⟶ realCond`, `F G : P ⟶ P` and `e₀ e₁ : 𝟙_ LightCondAb ⟶ P` satisfying the four
identities of REFS/03 §3, with `e₀ ≫ f = u`.

Concretely (for `u` the constant `r : ℝ`): `f` is the null sequence `e_n ↦ r·2^{-⌊log₂(n+1)⌋}`,
`F` is the averaging map `e_n ↦ e_{2n+1} + e_{2n+2}`, `G` is `e_n ↦ e_{2n+1}`, and `e₀` resp. `e₁`
are the images of the points `0` resp. `1` of `ℕ∪∞`.

Roadmap for the construction: `P = cokernel P_map` with `P_proj : ℤ[ℕ∪∞] ⟶ P` and
`P_homMk (A) (φ : ℤ[ℕ∪∞] ⟶ A) (h : P_map ≫ φ = 0) : P ⟶ A`.  Morphisms out of `ℤ[ℕ∪∞]` are
described by sections over `ℕ∪∞` via `Work.ANALYTIC.freeHomEquiv` (free/forget adjunction plus
Yoneda for the subcanonical coherent topology, see `Submission/Work/ANALYTIC/RealCond.lean`):
`f` comes from the continuous function `ℕ∪∞ → ℝ`, `n ↦ r·2^{-⌊log₂(n+1)⌋}`, `∞ ↦ 0`, where `r` is
the "value of `u`" obtained from `u` through the identification
`Hom(𝟙_ LightCondAb, realCond) ≃ Hom(ℤ[∗], realCond) ≃ C(∗,ℝ) ≃ ℝ` (𝟙_ LightCondAb is
definitionally the discrete condensed `ℤ`, and `ℤ[∗]` is `(free ℤ).obj (↧PUnit).toCondensed`);
`F`, `G` come from the continuous endomorphisms `n ↦ 2n+1`, `n ↦ 2n+2` of `ℕ∪∞` (they fix `∞`,
hence kill `ℤ[∞]` after `P_proj`); `e₀`, `e₁` are obtained from the same adjunction, and
`e₀ ≫ f = u` follows from the naturality of that identification (both sides evaluate to `r` at the
point `0`).  The identities are then checked on the generators `e_n ∈ P`, using
`⌊log₂(2n+2)⌋ = ⌊log₂(2n+3)⌋ = ⌊log₂(n+1)⌋ + 1`. -/
theorem exists_realNullSeq (u : 𝟙_ LightCondAb ⟶ realCond) :
    ∃ (f : P ⟶ realCond) (F G : P ⟶ P) (e₀ e₁ : 𝟙_ LightCondAb ⟶ P),
      (F ≫ f = f) ∧ (F ≫ oneMinusShift = oneMinusShift ≫ G) ∧ (e₀ ≫ G = e₁) ∧
      (e₀ ≫ oneMinusShift = e₀ - e₁) ∧ (e₀ ≫ f = u) := by
  -- the identification `ℤ[∗] ≅ 𝟙_`
  let ee : (free ℤ).obj NSPoint.toCondensed ≅ 𝟙_ LightCondAb := Work.ATOM.unitIso.symm
  -- the value of `u` at the point `e₀`
  let u' : (free ℤ).obj NSPoint.toCondensed ⟶ realCond := ee.hom ≫ u
  let r : ℝ := ev (secInv (freeHomEquiv NSPoint realCond u')) PUnit.unit
  -- the null sequence `g : ℤ[ℕ∪∞] ⟶ ℝ`
  let g : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ realCond :=
    (freeHomEquiv (ℕ∪{∞}) realCond).symm (sec (lamC r))
  have hg_section : freeHomEquiv (ℕ∪{∞}) realCond g = sec (lamC r) :=
    Equiv.apply_symm_apply _ _
  -- `g` vanishes at `∞`, hence descends to `P`
  have hg : P_map ≫ g = 0 := by
    apply (freeHomEquiv NSPoint realCond).injective
    rw [show P_map = zf.map LightCondensed.ι from rfl, freeHomEquiv_naturality, hg_section,
      freeHomEquiv_zero]
    exact realCond_map_zero LightCondensed.ι (lamC r) (fun x => by
      rw [show LightCondensed.ι x = ∞ from rfl]
      exact lamC_infty r)
  let f : P ⟶ realCond := P_homMk realCond g hg
  have hf : P_proj ≫ f = g := P_proj_P_homMk g hg
  -- the endomorphisms `F`, `G` of `P`
  let F0 : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ (free ℤ).obj (ℕ∪{∞}).toCondensed :=
    zf.map phiA + zf.map phiB
  let G0 : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ (free ℤ).obj (ℕ∪{∞}).toCondensed := zf.map phiA
  have hF : P_map ≫ (F0 ≫ P_proj) = 0 := by
    have h1 : P_map ≫ F0 = P_map + P_map := by
      show zf.map LightCondensed.ι ≫ (zf.map phiA + zf.map phiB) =
        zf.map LightCondensed.ι + zf.map LightCondensed.ι
      rw [Preadditive.comp_add, ← Functor.map_comp, ← Functor.map_comp,
        iota_comp phiA_apply_infty, iota_comp phiB_apply_infty]
    have hcond : P_map ≫ P_proj = 0 := cokernel.condition P_map
    rw [← Category.assoc, h1, Preadditive.add_comp, hcond, add_zero]
  let F : P ⟶ P := P_homMk P (F0 ≫ P_proj) hF
  have hF' : P_proj ≫ F = F0 ≫ P_proj := P_proj_P_homMk (F0 ≫ P_proj) hF
  have hG : P_map ≫ (G0 ≫ P_proj) = 0 := by
    have h2 : P_map ≫ G0 = P_map := by
      show zf.map LightCondensed.ι ≫ zf.map phiA = zf.map LightCondensed.ι
      rw [← Functor.map_comp, iota_comp phiA_apply_infty]
    have hcond : P_map ≫ P_proj = 0 := cokernel.condition P_map
    rw [← Category.assoc, h2, hcond]
  let G : P ⟶ P := P_homMk P (G0 ≫ P_proj) hG
  have hG' : P_proj ≫ G = G0 ≫ P_proj := P_proj_P_homMk (G0 ≫ P_proj) hG
  -- the points `e₀`, `e₁` of `P`
  let e₀ : 𝟙_ LightCondAb ⟶ P := ee.inv ≫ (zf.map ptZero ≫ P_proj)
  let e₁ : 𝟙_ LightCondAb ⟶ P := ee.inv ≫ (zf.map ptOne ≫ P_proj)
  -- `e₀ ≫ f = u`
  have hsec : realCond.obj.map ptZero.op (sec (lamC r)) = sec (constC NSPoint r) := by
    apply realCond_ext
    intro x
    rw [ev_map, show (ptZero : ↥(NSPoint).toTop → ↥(ℕ∪{∞}).toTop) x = OnePoint.some 0 from rfl]
    show lamC r (OnePoint.some 0) = constC NSPoint r x
    rw [lamC_zero, constC_apply]
  have hsec' : freeHomEquiv NSPoint realCond u' = sec (constC NSPoint r) := by
    apply realCond_ext
    intro x
    rw [show x = (PUnit.unit : ↥(NSPoint).toTop) from Subsingleton.elim x PUnit.unit]
    show ev (secInv (freeHomEquiv NSPoint realCond u')) PUnit.unit = constC NSPoint r PUnit.unit
    rw [constC_apply]
  have hu' : zf.map ptZero ≫ g = u' := by
    apply (freeHomEquiv NSPoint realCond).injective
    rw [freeHomEquiv_naturality, hg_section, hsec, ← hsec']
  refine ⟨f, F, G, e₀, e₁, ?_, ?_, ?_, ?_, ?_⟩
  · -- `F ≫ f = f`
    refine P_cancel ?_
    calc P_proj ≫ (F ≫ f) = (P_proj ≫ F) ≫ f := by rw [Category.assoc]
      _ = (F0 ≫ P_proj) ≫ f := by rw [hF']
      _ = F0 ≫ (P_proj ≫ f) := by rw [Category.assoc]
      _ = F0 ≫ g := by rw [hf]
      _ = g := F0_comp_g r
      _ = P_proj ≫ f := by rw [hf]
  · -- `F ≫ oneMinusShift = oneMinusShift ≫ G`
    refine P_cancel ?_
    calc P_proj ≫ (F ≫ oneMinusShift)
        = (P_proj ≫ F) ≫ oneMinusShift := by rw [Category.assoc]
      _ = (F0 ≫ P_proj) ≫ oneMinusShift := by rw [hF']
      _ = F0 ≫ (P_proj ≫ oneMinusShift) := by rw [Category.assoc]
      _ = F0 ≫ (oneMinusShift' ≫ P_proj) := by rw [P_proj_oneMinusShift]
      _ = (F0 ≫ oneMinusShift') ≫ P_proj := by rw [Category.assoc]
      _ = (oneMinusShift' ≫ zf.map phiA) ≫ P_proj := by rw [F0_oneMinusShift_comm]
      _ = oneMinusShift' ≫ (zf.map phiA ≫ P_proj) := by rw [Category.assoc]
      _ = oneMinusShift' ≫ (P_proj ≫ G) := by rw [hG']
      _ = (oneMinusShift' ≫ P_proj) ≫ G := by rw [← Category.assoc]
      _ = (P_proj ≫ oneMinusShift) ≫ G := by rw [← P_proj_oneMinusShift]
      _ = P_proj ≫ (oneMinusShift ≫ G) := by rw [Category.assoc]
  · -- `e₀ ≫ G = e₁`
    show (ee.inv ≫ (zf.map ptZero ≫ P_proj)) ≫ G = ee.inv ≫ (zf.map ptOne ≫ P_proj)
    rw [Category.assoc]
    congr 1
    calc zf.map ptZero ≫ P_proj ≫ G = zf.map ptZero ≫ (G0 ≫ P_proj) := by rw [hG']
      _ = (zf.map ptZero ≫ G0) ≫ P_proj := by rw [Category.assoc]
      _ = (zf.map ptZero ≫ zf.map phiA) ≫ P_proj := rfl
      _ = zf.map (ptZero ≫ phiA) ≫ P_proj := by rw [Functor.map_comp]
      _ = zf.map ptOne ≫ P_proj := by rw [ptZero_phiA]
  · -- `e₀ ≫ oneMinusShift = e₀ - e₁`
    have hkey : (zf.map ptZero ≫ P_proj) ≫ oneMinusShift =
        (zf.map ptZero ≫ P_proj) - (zf.map ptOne ≫ P_proj) := by
      calc (zf.map ptZero ≫ P_proj) ≫ oneMinusShift
          = zf.map ptZero ≫ (P_proj ≫ oneMinusShift) := by rw [Category.assoc]
        _ = zf.map ptZero ≫ (oneMinusShift' ≫ P_proj) := by rw [P_proj_oneMinusShift]
        _ = (zf.map ptZero ≫ oneMinusShift') ≫ P_proj := by rw [Category.assoc]
        _ = (zf.map ptZero - zf.map ptOne) ≫ P_proj := by
              rw [show oneMinusShift' = 𝟙 _ - zf.map LightProfinite.shift from rfl,
                Preadditive.comp_sub, Category.comp_id, ← Functor.map_comp, ptZero_shift]
        _ = (zf.map ptZero ≫ P_proj) - (zf.map ptOne ≫ P_proj) := by rw [Preadditive.sub_comp]
    calc (ee.inv ≫ (zf.map ptZero ≫ P_proj)) ≫ oneMinusShift
        = ee.inv ≫ ((zf.map ptZero ≫ P_proj) ≫ oneMinusShift) := by rw [Category.assoc]
      _ = ee.inv ≫ ((zf.map ptZero ≫ P_proj) - (zf.map ptOne ≫ P_proj)) := by rw [hkey]
      _ = (ee.inv ≫ (zf.map ptZero ≫ P_proj)) - (ee.inv ≫ (zf.map ptOne ≫ P_proj)) := by
            rw [Preadditive.comp_sub]
  · -- `e₀ ≫ f = u`
    have hkey : (zf.map ptZero ≫ P_proj) ≫ f = u' := by
      calc (zf.map ptZero ≫ P_proj) ≫ f = zf.map ptZero ≫ (P_proj ≫ f) := by
            rw [Category.assoc]
        _ = zf.map ptZero ≫ g := by rw [hf]
        _ = u' := hu'
    calc (ee.inv ≫ (zf.map ptZero ≫ P_proj)) ≫ f
        = ee.inv ≫ ((zf.map ptZero ≫ P_proj) ≫ f) := by rw [Category.assoc]
      _ = ee.inv ≫ u' := by rw [hkey]
      _ = u := by
            rw [show u' = ee.hom ≫ u from rfl, ← Category.assoc, ee.inv_hom_id, Category.id_comp]

end Work.ANALYTIC
