import Mathlib
import Submission.Work.StemsB.Rat.CollarSplit
import Submission.Work.StemsB.Rat.CollarDefs
import Submission.Work.StemsB.Rat.CollarSuspClass
import Submission.Work.StemsB.pairDelta_mixedCup_general_R

/-!
# The `δ`-computation for the `s`-part of the collar splitting

For the collar pair `(Q, C) = (↥(sphLoopBig b) × Y, sphLoopCollarProd b Y)`, a Thom class `τ`, a
suspension class `s` with `δ s = τ` (`Work.StemsB.Rat.CollarTransgresses`), and the transgression
coefficient map `Σ = collarSigma` defined by `π^*(Σ x) ⌣ τ = δ x`, the `s`-part
`collarSPart x = (-1)^{m+1} π^*(Σ x) ⌣ s` satisfies

  `δ (collarSPart x) = δ x`.

This is the hypothesis of `Work.StemsB.Rat.collarSplit_of_delta`, and it is proved by the one-sided
derivation formula `Work.Sph3Disc.pairDelta_mixedCup_general`
(`δ(x|_C ⌣ y) = (-1)^{|x|} x ⌣ δ y`): the two Koszul signs (one from the derivation, one from the
normalisation of `collarSPart`) cancel, and `δ s = τ` converts the result into `π^*(Σ x) ⌣ τ`,
which is `δ x` by the defining property of `Σ`.

The only delicate point is the bookkeeping of the degrees: the connecting homomorphism lives in
degrees `n + 1`, and the arithmetic identities `(m+1) + (b-1) = m + b` and `b - 1 + 1 = b` are not
definitional.  This is handled by the transport lemmas `pairδ_eqToHom_homology`,
`mixedCup_eqToHom_homology` and `eqToHom_homology_trans_apply` below, all proved by `cases` on the
index equality.

With this lemma, `Work.StemsB.Rat.collarSplit_of_delta` applies verbatim and gives the splitting of the
collar cohomology along the suspension class (`D2_PLAN.md` §2 item 3).

Two formalisation traps, for the record (both cost a serious amount of debugging time):

* in the main computation, *never* apply a generic linearity/smul lemma (`map_zsmul`, `map_smul`,
  `smul_smul`, ...) by `rw`/`exact` directly: matching such a lemma against the goal asks the
  elaborator to solve a `FunLike`/`AddMonoidHomClass`-flavoured type class problem *while the
  metavariables of the lemma are still open*, and on the (very large) `↥(relComplex ...).homology n`
  terms this does not terminate in any reasonable heartbeat budget.  The fix used here is to isolate
  the linearity steps as specialised lemmas (`pairδ_map_zsmul`, `neg_one_pow_smul_cancel`), proved
  once in a small context, and then to apply them from the big goal through `congrArg` under the
  outer transports (the local helpers `congr_Tk`, `congr_Tbk`), whose statements are matched
  syntactically;
* `eqToHom_homology_trans_apply` takes the *index* equalities (not the transported `congrArg …`
  equalities): its conclusion then mentions `congrArg (fun t => K.homology t) (h.trans h')` with the
  same `h`, `h'` as in the goal.  Passing already-transported equalities makes the elaborator try to
  reverse-engineer `h` from `Eq.trans`, which fails outright.
-/

open CategoryTheory CategoryTheory.Limits

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.StemsB.Rat

noncomputable section

/-! ## The collar model, with abbreviations -/

/-- The total space `Q = ↥(sphLoopBig b) × Y` of the collar model. -/
abbrev CollQ (b : ℕ) (Y : Type) [TopologicalSpace Y] : TopCat :=
  TopCat.of (↥(sphLoopBig b) × Y)

/-- The collar `C ⊆ Q`. -/
abbrev CollA (b : ℕ) (Y : Type) [TopologicalSpace Y] : Set (CollQ b Y) :=
  sphLoopCollarProd b Y

/-- The collar as a topological space. -/
abbrev CollC (b : ℕ) (Y : Type) [TopologicalSpace Y] : TopCat :=
  TopCat.of ↥(sphLoopCollarProd b Y)

/-- The singular cochain complex of the collar. -/
abbrev CollKC (b : ℕ) (Y : Type) [TopologicalSpace Y] : CochainComplex (ModuleCat ℚ) ℕ :=
  Work.Cohomology.singularCochainComplex ℚ (CollC b Y)

/-- The relative cochain complex of the collar pair. -/
abbrev CollRC (b : ℕ) (Y : Type) [TopologicalSpace Y] : CochainComplex (ModuleCat ℚ) ℕ :=
  Work.Cohomology.relComplex ℚ (CollQ b Y) (CollA b Y)

/-! ## Transports along equalities of degrees -/

/-- **Two degree transports compose.**  The (definitionally equal) middle degree is the one of the
intermediate homology module. -/
lemma eqToHom_homology_trans_apply (K : CochainComplex (ModuleCat ℚ) ℕ) {i j k : ℕ}
    (h : i = j) (h' : j = k) (z : K.homology i) :
    (eqToHom (congrArg (fun t => K.homology t) h') : K.homology j ⟶ K.homology k)
        ((eqToHom (congrArg (fun t => K.homology t) h) : K.homology i ⟶ K.homology j) z)
      = (eqToHom (congrArg (fun t => K.homology t) (h.trans h')) : K.homology i ⟶ K.homology k)
        z := by
  cases h
  cases h'
  simp

/-- **A degree transport along a self-equality is the identity.** -/
lemma eqToHom_homology_self (K : CochainComplex (ModuleCat ℚ) ℕ) (i : ℕ) (h : i = i)
    (z : K.homology i) :
    (eqToHom (congrArg (fun t => K.homology t) h) : K.homology i ⟶ K.homology i) z = z := by
  rw [Subsingleton.elim h rfl]
  simp

/-- **The connecting homomorphism of a pair is natural in the degree.** -/
lemma pairδ_eqToHom_homology {X : TopCat} {A : Set X} {i i' : ℕ} (h : i = i')
    (y : (Work.Cohomology.singularCochainComplex ℚ (TopCat.of A)).homology i) :
    (Work.Cohomology.pairδ ℚ X A i').hom
        (eqToHom (congrArg
          (fun t => (Work.Cohomology.singularCochainComplex ℚ (TopCat.of A)).homology t) h) y)
      = eqToHom (congrArg (fun t => (Work.Cohomology.relComplex ℚ X A).homology t)
            (congrArg (fun t => t + 1) h))
          ((Work.Cohomology.pairδ ℚ X A i).hom y) := by
  cases h
  simp

/-- **The mixed cup product is natural in the degree of the relative argument.** -/
lemma mixedCup_eqToHom_homology (X : TopCat) (A : Set X) (p : ℕ) {i i' : ℕ} (h : i = i')
    (x : (Work.Cohomology.singularCochainComplex ℚ X).homology p)
    (z : (Work.Cohomology.relComplex ℚ X A).homology i) :
    (Work.Cohomology.mixedCupR ℚ X A p i') x
        (eqToHom (congrArg (fun t => (Work.Cohomology.relComplex ℚ X A).homology t) h) z)
      = eqToHom (congrArg (fun t => (Work.Cohomology.relComplex ℚ X A).homology (p + t)) h)
          ((Work.Cohomology.mixedCupR ℚ X A p i) x z) := by
  cases h
  simp

/-- `(-1)^k · (-1)^k = 1`. -/
lemma neg_one_pow_mul_self (k : ℕ) : ((-1 : ℚ)) ^ k * ((-1 : ℚ)) ^ k = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨k, by ring⟩

/-- **Linearity of the connecting homomorphism in the class** (the `smul` form, isolated so that
no type class search on the underlying linear map is needed in the main computation). -/
lemma pairδ_map_smul {X : TopCat} {A : Set X} (n : ℕ) (c : ℚ)
    (y : (Work.Cohomology.singularCochainComplex ℚ (TopCat.of A)).homology n) :
    (Work.Cohomology.pairδ ℚ X A n).hom (c • y)
      = c • (Work.Cohomology.pairδ ℚ X A n).hom y :=
  map_smul _ c y

/-- **Cancellation of two equal signs** `(-1)^k`. -/
lemma neg_one_pow_smul_cancel (k : ℕ) {M : Type} [AddCommGroup M] [Module ℚ M] (x : M) :
    ((-1 : ℚ) ^ k) • (((-1 : ℚ) ^ k) • x) = x := by
  rw [smul_smul, neg_one_pow_mul_self, one_smul]

/-! ## The collar projection is the restriction of the projection to the total space -/

/-- **`collarProjC` is the composite of the restriction of the collar pair with the projection of
the total space to `Y`.** -/
lemma collarProjC_eq_restr (b : ℕ) (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    collarProjC b Y n
      = ((HomologicalComplex.homologyMap
            (Work.Cohomology.restr ℚ (CollQ b Y) (CollA b Y)) n).hom).comp
          (Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ n).hom := by
  have h1 : (⟨fun q : ↥(sphLoopCollarProd b Y) => q.1.2, by fun_prop⟩ :
        C(↥(sphLoopCollarProd b Y), Y))
      = (collarProjY (Y := Y) b).comp ⟨Subtype.val, continuous_subtype_val⟩ := by
    ext q; rfl
  have h2 : (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of ↥(sphLoopCollarProd b Y) ⟶ TopCat.of (↥(sphLoopBig b) × Y))
      = Work.Cohomology.subtypeIncl (TopCat.of (↥(sphLoopBig b) × Y))
          (sphLoopCollarProd b Y) := by
    rfl
  rw [collarProjC, h1, Work.Thom.CohMap_comp]
  rw [show Work.Thom.CohMap ⟨Subtype.val, continuous_subtype_val⟩ ℚ n
      = HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ (CollQ b Y) (CollA b Y)) n
      from by
    rw [Work.Thom.CohMap, Work.Cohomology.singularCohomologyMap,
      Work.Cohomology.restr, h2]]
  exact ModuleCat.hom_comp _ _

/-- **The element form of `collarProjC_eq_restr`**, valid with either spelling of the homology of
the total space. -/
lemma collarProjC_eq_restr_apply (b : ℕ) (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (y : Work.Thom.Coh ℚ n Y) :
    collarProjC b Y n y
      = (HomologicalComplex.homologyMap
            (Work.Cohomology.restr ℚ (CollQ b Y) (CollA b Y)) n).hom
          ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ n).hom y) := by
  rw [collarProjC_eq_restr]
  rfl

/-! ## The computation rules of the degree comparisons -/

/-- **The computation rule of `collarRelEqS`.** -/
lemma collarRelEqS_apply (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] (m : ℕ)
    (hj : (m + 1) + (b - 1) = m + b) (z : (CollKC b Y).homology ((m + 1) + (b - 1))) :
    collarRelEqS b hb Y m z = eqToHom (congrArg (fun t => (CollKC b Y).homology t) hj) z := by
  rw [collarRelEqS]
  rfl

/-- **The computation rule of `collarRelEq`.** -/
lemma collarRelEq_apply (b : ℕ) (Y : Type) [TopologicalSpace Y] (m : ℕ)
    (hj : (m + b) + 1 = (m + 1) + b) (z : (CollRC b Y).homology ((m + b) + 1)) :
    collarRelEq (Y := Y) b m z = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hj) z := by
  rw [collarRelEq]
  rfl

/-- **The bridge between `mixedCupC` and `mixedCup`.** -/
lemma mixedCupC_eq_mixedCup (b : ℕ) (Y : Type) [TopologicalSpace Y] (m n : ℕ) :
    Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) m n
      = Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) m n := rfl

/-! ## The `δ`-computation -/

theorem collarDelta_collarSPart (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(Work.StemsB.sphLoopBig b) × Y)
          (Work.StemsB.sphLoopCollarProd b Y))
    (hτ : Work.StemsB.Rat.CollarThom (Y := Y) b τ)
    (s : (Work.Cohomology.singularCochainComplex ℚ
          (TopCat.of ↥(Work.StemsB.sphLoopCollarProd b Y))).homology (b - 1))
    (hs : Work.StemsB.Rat.CollarTransgresses b hb (Y := Y) s τ)
    (m : ℕ)
    (x : (Work.Cohomology.singularCochainComplex ℚ
          (TopCat.of ↥(Work.StemsB.sphLoopCollarProd b Y))).homology (m + b)) :
    Work.StemsB.Rat.collarDelta (Y := Y) b m (Work.StemsB.Rat.collarSPart b hb (Y := Y) τ hτ s m x)
      = Work.StemsB.Rat.collarDelta (Y := Y) b m x := by
  have hba : b - 1 + 1 = b := by omega
  have hk : (m + 1) + (b - 1) = m + b := by omega
  have hcar : (m + b) + 1 = (m + 1) + b := by omega
  have hB : (m + 1) + b = (m + 1) + ((b - 1) + 1) := by omega
  have hK : ((m + 1) + (b - 1)) + 1 = (m + b) + 1 := by omega
  -- the transgression condition
  have hs' := hs
  unfold CollarTransgresses at hs'
  have htrans : (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom s
      = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hba.symm) τ := hs'
  -- the abbreviations
  set sx := collarSigma b hb (Y := Y) τ hτ m x with hsx
  set xq := (Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ (m + 1)).hom sx with hxq
  set w := (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + 1) (b - 1))
      ((HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ (CollQ b Y) (CollA b Y))
        (m + 1)).hom xq) s with hw
  -- the derivation property
  have hder : (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) ((m + 1) + (b - 1))).hom w
      = ((-1 : ℚ) ^ (m + 1)) • ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (m + 1)
          ((b - 1) + 1)) xq ((Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom s)) :=
    Work.StemsB.pairDelta_mixedCup_general_R ℚ (CollQ b Y) (CollA b Y) (m + 1) (b - 1) xq s
  -- the defining property of the transgression coefficient map
  have hsigma : (Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (m + 1) b) xq τ
      = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hcar)
          (collarDelta (Y := Y) b m x) := by
    have h1 := collarSigma_spec b hb (Y := Y) τ hτ m x
    rw [collarPhi_apply] at h1
    rw [← hsx, ← hxq] at h1
    rw [mixedCupC_eq_mixedCup] at h1
    rw [h1]
    exact collarRelEq_apply b Y m hcar (collarDelta (Y := Y) b m x)
  -- the computation rule of the `s`-part
  have hsp : collarSPart b hb (Y := Y) τ hτ s m x
      = eqToHom (congrArg (fun t => (CollKC b Y).homology t) hk)
          (((-1 : ℚ) ^ (m + 1)) • w) := by
    rw [collarSPart_apply b hb (Y := Y) τ hτ s m x]
    rw [← hsx, collarProjC_eq_restr_apply, ← hxq, ← hw]
    exact collarRelEqS_apply b hb Y m hk _
  -- congruence under the two outer transports
  have congr_Tk : ∀ {u v : (CollRC b Y).homology (((m + 1) + (b - 1)) + 1)}, u = v →
      eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK) u
        = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK) v :=
    fun h => congrArg (fun z => eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK) z) h
  have congr_Tbk : ∀ {u v : (CollRC b Y).homology ((m + 1) + b)}, u = v →
      eqToHom (congrArg (fun t => (CollRC b Y).homology t) (hB.trans hK)) u
        = eqToHom (congrArg (fun t => (CollRC b Y).homology t) (hB.trans hK)) v :=
    fun h => congrArg (fun z =>
      eqToHom (congrArg (fun t => (CollRC b Y).homology t) (hB.trans hK)) z) h
  calc (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (m + b)).hom
        (collarSPart b hb (Y := Y) τ hτ s m x)
      = (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (m + b)).hom
          (eqToHom (congrArg (fun t => (CollKC b Y).homology t) hk)
            (((-1 : ℚ) ^ (m + 1)) • w)) := by rw [hsp]
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK)
          ((Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y)
            ((m + 1) + (b - 1))).hom (((-1 : ℚ) ^ (m + 1)) • w)) :=
        pairδ_eqToHom_homology (X := CollQ b Y) (A := CollA b Y)
          (i := (m + 1) + (b - 1)) (i' := m + b) hk (((-1 : ℚ) ^ (m + 1)) • w)
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK)
          (((-1 : ℚ) ^ (m + 1)) •
            ((Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y)
              ((m + 1) + (b - 1))).hom w)) :=
        congr_Tk (pairδ_map_smul (X := CollQ b Y) (A := CollA b Y)
          ((m + 1) + (b - 1)) ((-1 : ℚ) ^ (m + 1)) w)
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK)
          (((-1 : ℚ) ^ (m + 1)) • (((-1 : ℚ) ^ (m + 1)) •
            ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y)
              (m + 1) ((b - 1) + 1)) xq
              ((Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom s)))) :=
        congr_Tk (by rw [hder])
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK)
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y)
            (m + 1) ((b - 1) + 1)) xq
              ((Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom s)) :=
        congr_Tk (neg_one_pow_smul_cancel (m + 1) _)
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK)
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y)
            (m + 1) ((b - 1) + 1)) xq
            (eqToHom (congrArg (fun t => (CollRC b Y).homology t) hba.symm) τ)) :=
        congr_Tk (by rw [htrans])
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t) hK)
          (eqToHom (congrArg (fun t => (CollRC b Y).homology t) hB)
            ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (m + 1) b) xq τ)) :=
        congr_Tk (mixedCup_eqToHom_homology (CollQ b Y) (CollA b Y) (m + 1) hba.symm xq τ)
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t) (hB.trans hK))
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (m + 1) b) xq τ) :=
        eqToHom_homology_trans_apply (K := CollRC b Y) (h := hB) (h' := hK) (z := _)
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t) (hB.trans hK))
          (eqToHom (congrArg (fun t => (CollRC b Y).homology t) hcar)
            (collarDelta (Y := Y) b m x)) :=
        congr_Tbk hsigma
    _ = eqToHom (congrArg (fun t => (CollRC b Y).homology t)
          (hcar.trans (hB.trans hK))) (collarDelta (Y := Y) b m x) :=
        eqToHom_homology_trans_apply (K := CollRC b Y) (h := hcar)
          (h' := hB.trans hK) (z := _)
    _ = collarDelta (Y := Y) b m x :=
        eqToHom_homology_self (CollRC b Y) ((m + b) + 1) (hcar.trans (hB.trans hK))
          (collarDelta (Y := Y) b m x)

end

end Work.StemsB.Rat
