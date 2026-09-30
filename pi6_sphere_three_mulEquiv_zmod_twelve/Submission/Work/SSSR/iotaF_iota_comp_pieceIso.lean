import Mathlib
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.serreE1PieceExplicit
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.SSSR.iotaF_chainMap
import Submission.Work.SSSR.iotaF_isCycle
import Submission.Work.SSSR.serreE1PieceIsoZero
import Submission.Work.SSSR.serreE1StepAux
import Submission.Work.SSSR.sigmaVert_face
import Submission.Work.SSSR.pieceIso_peel
import Submission.Work.SSSR.IotaChain.basic
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## The sign of the tower -/

/-- The sign `c_P = (-1)^{P(P+1)/2}` of the tower comparison, defined recursively. -/
def iotaSign : ℕ → ℤ :=
  fun n => Nat.rec 1 (fun k acc => ((-1 : ℤ) ^ (k+1)) * acc) n

@[simp] lemma iotaSign_zero : iotaSign 0 = 1 := rfl

lemma iotaSign_succ (n : ℕ) : iotaSign (n+1) = ((-1 : ℤ) ^ (n+1)) * iotaSign n := rfl

lemma iotaSign_neg_one_pow_or (n : ℕ) : ((-1 : ℤ) ^ n = 1 ∨ (-1 : ℤ) ^ n = -1) := by
  rcases Nat.even_or_odd n with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow

lemma iotaSign_or (n : ℕ) : iotaSign n = 1 ∨ iotaSign n = -1 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [iotaSign_succ]
    rcases ih with h | h
    · rw [h, mul_one]
      exact iotaSign_neg_one_pow_or (k+1)
    · rw [h, mul_neg, mul_one]
      rcases iotaSign_neg_one_pow_or (k+1) with hh | hh <;> rw [hh] <;> norm_num

/-! ## The chain-level induction statement -/

/-- The statement proved by induction: `ε_σ` sends the class of `ι_σ z` to `iotaSign P` times the
class of `z`, for every base point `b` and every cycle `z` of the fibre over `b`. -/
def ChainStatement (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (P : ℕ)
    (c : ℤ) : Prop :=
  ∀ (b : B)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk P) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b)
    (t : ℕ) (z : (Work.SSSR.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0)
    (hy : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (P+t)
            ((ComplexShape.down ℕ).next (P+t))))
            ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
              (Work.SSSR.liftFam_proj p hfib) P b σ h t)) z) = 0),
    (Work.SSSR.fibreConj p h t)
      ((Work.SSSR.serreE1PieceIso p hfib P t σ).hom
        (HomologicalComplex.homologyπ (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ) (P+t)
          ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cyclesMk
            ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
              (Work.SSSR.liftFam_proj p hfib) P b σ h t)) z)
            ((ComplexShape.down ℕ).next (P+t)) rfl hy)))
    = c • ((Work.SSSR.fibreCC p b).homologyπ t
          ((Work.SSSR.fibreCC p b).cyclesMk z
            ((ComplexShape.down ℕ).next t) rfl hz))

/-- Base case `P = 0`. -/
theorem chainStatement_zero (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) :
    ChainStatement (R := R) p hfib 0 (iotaSign 0) := by
  rw [iotaSign_zero]
  intro b σ h t z hz hy
  simpa using Work.SSSR.IotaChain.serreE1PieceIsoZero_chain p hfib b σ h t z hz hy

/-- Induction step: from the statement at `s`, the statement at `s+1`, with the sign multiplied
by `(-1)^{s+1}`. -/
theorem chainStatement_succ (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) (s : ℕ) (c : ℤ)
    (ih : ChainStatement (R := R) p hfib s c) :
    ChainStatement (R := R) p hfib (s+1) (((-1 : ℤ)^(s+1)) * c) := by
  intro b σ h t z hz hy
  have h2ne : Fin.last (s+1) ≠ (0 : Fin (s+2)) := by
    intro hh; have hv := congrArg Fin.val hh; simp [Fin.last] at hv
  have hsv : Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ)
      = Work.SSSR.sigmaVert σ := Work.SSSR.sigmaVert_face (Fin.last (s+1)) h2ne σ
  have h' : Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) = b :=
    hsv.trans h
  have hcyc' : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ)).d (s+t)
        ((ComplexShape.down ℕ).next (s+t))))
        ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
          (Work.SSSR.liftFam_proj p hfib) s b
          (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' t)) z) = 0 :=
    Work.SSSR.IotaChain.iotaF_cycle p hfib s t b
      (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' z hz
  set zv : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X ((s+1)+t) :=
    (ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
      (Work.SSSR.liftFam_proj p hfib) (s+1) b σ h t)) z with hzv
  set wv : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
      (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ))).X (s+t) :=
    (ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib)
      (Work.SSSR.liftFam_proj p hfib) s b
      (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' t)) z with hwv
  have hpeel := Work.SSSR.IotaChain.hornCok_d_iotaT_chain p hfib s t b σ h h' z hz
  have hstep := Work.SSSR.pieceIso_peel p hfib s t b σ zv hy wv hcyc' hpeel
  change (Work.SSSR.fibreConj p h t)
      ((Work.SSSR.serreE1PieceIso p hfib (s+1) t σ).hom
        (HomologicalComplex.homologyπ (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ) ((s+1)+t)
          ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p) σ).f ((s+1)+t))) zv)
            ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hy)))
    = ((-1 : ℤ)^(s+1) * c) • ((Work.SSSR.fibreCC p b).homologyπ t
          ((Work.SSSR.fibreCC p b).cyclesMk z ((ComplexShape.down ℕ).next t) rfl hz))
  rw [hstep, map_zsmul]
  set Y : (Work.SSSR.Cohomology.singularChains R
      (TopCat.of (Work.SSSR.StemsB.fibre p (Work.SSSR.sigmaVert
        (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ))))).homology t :=
    (Work.SSSR.serreE1PieceIso p hfib s t
        (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ)).hom
      (HomologicalComplex.homologyπ (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
          (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ)) (s+t)
        ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
          (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ)).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p)
            (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ)).f (s+t))) wv)
          ((ComplexShape.down ℕ).next (s+t)) rfl hcyc')) with hY
  have hEq : (Work.SSSR.fibreConj p hsv t)
      = (CategoryTheory.eqToIso (congrArg (fun x : B => (Work.SSSR.Cohomology.singularChains R
          (TopCat.of (Work.SSSR.StemsB.fibre p x))).homology t)
          (Work.SSSR.sigmaVert_face (Fin.last (s+1)) h2ne σ))).hom := by
    rw [Work.SSSR.fibreConj_eq]
  have htrans : (Work.SSSR.fibreConj p h t)
        ((CategoryTheory.eqToIso (congrArg (fun x : B => (Work.SSSR.Cohomology.singularChains R
            (TopCat.of (Work.SSSR.StemsB.fibre p x))).homology t)
            (Work.SSSR.sigmaVert_face (Fin.last (s+1)) h2ne σ))).hom Y)
      = (Work.SSSR.fibreConj p h' t) Y := by
    rw [← hEq]
    have ht := Work.SSSR.fibreConj_trans (R := R) p hsv h t
    have hb : (Work.SSSR.fibreConj p h t) ((Work.SSSR.fibreConj p hsv t) Y)
        = (Work.SSSR.fibreConj p (hsv.trans h) t) Y := by
      have hc := congrArg (fun (φ : (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert
          (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ))).homology t ⟶
          (Work.SSSR.fibreCC p b).homology t) => (ConcreteCategory.hom φ) Y) ht
      simpa only [ConcreteCategory.comp_apply] using hc
    calc (Work.SSSR.fibreConj p h t) ((Work.SSSR.fibreConj p hsv t) Y)
        = (Work.SSSR.fibreConj p (hsv.trans h) t) Y := hb
      _ = (Work.SSSR.fibreConj p h' t) Y := by
            rw [show hsv.trans h = h' from Subsingleton.elim _ _]
  have hih : (Work.SSSR.fibreConj p h' t) Y = c • ((Work.SSSR.fibreCC p b).homologyπ t
      ((Work.SSSR.fibreCC p b).cyclesMk z ((ComplexShape.down ℕ).next t) rfl hz)) :=
    ih b (SSet.stdSimplex.δ (n := s) (Fin.last (s+1)) ≫ σ) h' t z hz hcyc'
  rw [htrans, hih, smul_smul]

/-- **The Eilenberg–Zilber chain map `ι_σ` is, up to a dimension-dependent sign, a section of the
piece isomorphism `ε_σ`, on HOMOLOGY CLASSES OF ARBITRARY CYCLES `z`.**

For every simplex `σ` of `Sing B`, every chain `z` of the fibre over `σ(v₀)` which is a cycle, with
`ι_σ z` a cycle in the σ-piece, the iterated last-face connecting map `ε_σ = serreE1PieceIso`
sends the class of `ι_σ z` to `±` the class of `z`; the sign depends only on the dimension `s`
of `σ`.

The statement is deliberately about an arbitrary CHAIN `z` (not a simplex): for a simplex of even
degree `≥ 2` the hypothesis `∂z = 0` is unsatisfiable, so the simplex-level version
(`Work.SSSR.serreE1PieceIso_iota_deg`) is vacuous in those degrees and cannot be used.  For chains,
`{z : ∂z = 0}` is exactly the set of cycle representatives of `H_t(F)`, so this statement is
equivalent to the morphism-level identity `H(ι_σ) ≫ ε_σ = c s • 𝟙`. -/
theorem iotaF_iota_comp_pieceIso {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hfib : Work.SSSR.StemsB.IsSerreFibration p) :
    ∃ c : ℕ → ℤ, (∀ s : ℕ, c s = 1 ∨ c s = -1) ∧
      ∀ (s t : ℕ)
        (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})) ⟶ Work.SSSR.sSing B)
        (z : (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert σ)).X t)
        (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert σ)).d t
                ((ComplexShape.down ℕ).next t))) z = 0)
        (hy : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (s+t)
                ((ComplexShape.down ℕ).next (s+t))))
                ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
                  (Work.SSSR.liftFam_proj p hfib) s (Work.SSSR.sigmaVert σ) σ rfl t)) z) = 0),
      (ModuleCat.Hom.hom (Work.SSSR.serreE1PieceIso p hfib s t σ).hom)
          ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).homologyπ (s+t)
            ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cyclesMk
              ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib)
                (Work.SSSR.liftFam_proj p hfib) s (Work.SSSR.sigmaVert σ) σ rfl t)) z)
              ((ComplexShape.down ℕ).next (s+t)) rfl hy))
        = c s • ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert σ)).homologyπ t
            ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert σ)).cyclesMk z
              ((ComplexShape.down ℕ).next t) rfl hz)) := by
  have hall : ∀ s, ChainStatement (R := R) p hfib s (iotaSign s) := by
    intro s
    induction s with
    | zero => exact chainStatement_zero p hfib
    | succ k ih => rw [iotaSign_succ]; exact chainStatement_succ p hfib k (iotaSign k) ih
  refine ⟨iotaSign, iotaSign_or, ?_⟩
  intro s t σ z hz hy
  have h := hall s (Work.SSSR.sigmaVert σ) σ rfl t z hz hy
  simp only [Work.SSSR.fibreConj_rfl, CategoryTheory.id_apply] at h
  exact h

end

end Work.SSSR
