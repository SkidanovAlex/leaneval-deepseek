import Submission.Work.Tubular.CapCupAdjunction
import Submission.Work.Tubular.relKronecker_chain
import Submission.Work.Cohomology.cup1Identity

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The mixed cap/cup adjunction against the *relative* Kronecker pairing

`Work.Tubular.kronH_mixedCup_relCapPair` (`Submission/Work/Tubular/CapCupAdjunction.lean`) proves the
mixed cap/cup adjunction only in the form in which the relative homology class `c` has an *absolute*
lift `c'` (`hc : π c' = c`).  In the application to the Pontryagin–Thom collapse this hypothesis is
vacuous: for the normal bundle of a compact `8`-manifold the group `H_{k+8}` of the total space is
zero, so the only class admitting an absolute lift is `0` (see `README.md` §21.1).

The right-hand side of the adjunction is therefore the **relative Kronecker pairing**
`Work.Tubular.relKronH` (`Submission/Work/Tubular/relKronecker_chain.lean`):

  `⟨x, β ⌢ c⟩ = ⟨x ⌣ β, c⟩`   with   `β ∈ H^p(X,A)`, `c ∈ H_{p+q}(X,A)`, `x ∈ H^q(X)`

and both pairings computed against the *relative* group `H_{p+q}(X,A)`.  This module proves this
corrected form (`Work.Tubular.kronH_mixedCup_relKronH`).  The graded sign `(-1)^{pq}` (which makes
`x ⌣ β` and `β ⌣ x` agree) is `+1` under the hypothesis `Even (p*q)`; the application has `q = 8`.

## Contents

* the chain-level identity `Work.Tubular.kronecker_cap_cup_comm_rel` in general degrees, on an
  arbitrary chain whose boundary is trivial in `C_*(X,A)` (the general form of
  `Work.Cohomology.kronecker_cap_cup_comm`);
* the transport lemmas `Work.Tubular.kronecker_cast`, `relCocycleOf_irrel`, `relClassOf_congr`,
  `relDiffLM_cast`, `relClassOf_cast`;
* **`Work.Tubular.kronH_mixedCup_relKronH`**.

## Two conventions that matter (and that are easy to get wrong)

* `relCapPair X A p q` lives in degrees `p + q` (relative *homology*), while `mixedCup X A q p`
  lands in degree `q + p` (relative *cohomology*).  The statement therefore carries the transport
  `(Nat.add_comm q p) ▸ mixedCup …`; compare `README.md` §18bis.
* the lift of a relative cycle that `Work.Tubular.relKronH_apply` asks for is a lift of
  `relChains_cokernelIso (iCycles cc)`, produced from a lift of the cycle `iCycles cc` itself by
  `relChains_cokernelIso_canon_apply`.  The boundary of that lift is then automatically supported in
  `A`, because `relDualProj` is the degreewise component of the chain map `C_*(X) ⟶ C_*(X,A)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Tubular

noncomputable section

open Work.Cohomology

variable {X : TopCat} {A : Set X}

/-! ## Two elementary facts about relative cochains

These are the copies of `Work.Cohomology.app_map_naturality`,
`Work.Cohomology.cup1_mem_relKern_left` and
`Work.Cohomology.relKern_apply_eq_zero_of_relDualProj_eq_zero` living in this namespace: the chapter
is an *import island* (see `README.md` §19.1), and importing the module that holds the originals
would clash with `Work.Cohomology.relZEquiv_comm_apply`. -/

/-- Elementwise naturality of a map of simplicial sets. -/
lemma app_map_naturality {X Y : SSet} (f : X ⟶ Y) {a b : ℕ} (φ : ⦋a⦌ ⟶ ⦋b⦌) (τ : X _⦋b⦌) :
    f.app (Opposite.op ⦋a⦌) (X.map φ.op τ) = Y.map φ.op (f.app (Opposite.op ⦋b⦌) τ) := by
  have h := f.naturality φ.op
  exact congrArg (fun (g : X.obj (Opposite.op ⦋b⦌) ⟶ Y.obj (Opposite.op ⦋a⦌)) => g τ) h

/-- `cup1` of a relative cochain is a relative cochain: the homotopy between `α ⌣ β` and
`β ⌣ α` vanishes on chains supported in `A` whenever `α` is relative. -/
lemma cup1_mem_relKern_left (R : Type) [CommRing R] (X : TopCat) (A : Set X) {n m : ℕ}
    {α : Cochain R (TopCat.toSSet.obj X) n} (hα : α ∈ relKern R X A n)
    (β : Cochain R (TopCat.toSSet.obj X) m) :
    cup1 R (TopCat.toSSet.obj X) n m α β ∈ relKern R X A (n + m - 1) := by
  rw [relKern, LinearMap.mem_ker, restr, dualChainMap_f_hom, chainMap_f_eq]
  apply genEval_ext (X := TopCat.toSSet.obj (TopCat.of A))
  intro τ
  have hz : genEval R (TopCat.toSSet.obj (TopCat.of A))
      (0 : Cochain R (TopCat.toSSet.obj (TopCat.of A)) (n + m - 1)) τ = 0 := by
    simp [genEval]
  erw [genEval_dualMap, genEval_cup1, hz]
  refine Finset.sum_eq_zero (fun s _ => ?_)
  have h0 : genEval R (TopCat.toSSet.obj X) α
      ((TopCat.toSSet.obj X).map (Fface n m s.val (by have := s.isLt; omega)).op
        ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n + m - 1⦌) τ)) = 0 := by
    rw [← app_map_naturality]
    exact genEval_eq_zero_of_mem_relKern R X A α hα _
  rw [h0, mul_zero, zero_mul]

/-- A relative cochain vanishes on a chain whose class in `C_*(X,A)` is zero. -/
lemma relKern_apply_eq_zero_of_relDualProj_eq_zero (X : TopCat) (A : Set X) {k : ℕ}
    (φ : relKern ℤ X A k) (z : (singularChains ℤ X).X k)
    (hz : relDualProj X A k z = 0) : relDualLM X k φ.1 z = 0 := by
  have hmem : z ∈ LinearMap.range ((inclChains X A).f k).hom := by
    rw [← relDualProj_ker X A k]
    exact LinearMap.mem_ker.mpr hz
  obtain ⟨y, hy⟩ := hmem
  rw [← hy]
  exact (relDualKern_iff X A k φ.1).1 φ.2 y

/-! ## Transporting along an equality of degrees -/

/-- A function of both a degree and an element commutes with the transport of the element along an
equality of degrees.  (The generic form of `Work.Cohomology.cast_apply_aux`.) -/
lemma cast_apply {A B : ℕ → Type*} (f : ∀ n, A n → B n) {a b : ℕ} (h : a = b) (x : A a) :
    h ▸ f a x = f b (h ▸ x) := by cases h; rfl

/-- The Kronecker pairing commutes with the transport of its arguments along an equality of
degrees. -/
lemma kronecker_cast {R : Type} [CommRing R] {X : SSet} {n m : ℕ} (h : n = m)
    (γ : Cochain R X n) (z : ↑((X.chainComplex (ModuleCat.of R R)).X m)) :
    kronecker R X (h ▸ γ) z = kronecker R X γ (h.symm ▸ z) :=
  cast_linearMap_apply h γ z

/-- The differential of the relative cochain complex commutes with the transport of a relative
cochain along an equality of degrees. -/
lemma relDiffLM_cast {n m : ℕ} (h : n = m) (γ : relKern ℤ X A n) :
    relDiffLM ℤ X A m (h ▸ γ) = (congrArg (· + 1) h) ▸ (relDiffLM ℤ X A n γ) := by
  cases h; rfl

/-- The cocycle property of a relative cochain is preserved by the transport of the cochain along an
equality of degrees. -/
lemma relCocycleProof {n m : ℕ} (h : n = m) (γ : relKern ℤ X A n)
    (hγ : relDiffLM ℤ X A n γ = 0) : relDiffLM ℤ X A m (h ▸ γ) = 0 := by
  cases h; exact hγ

/-- The cycle associated with a relative cocycle does not depend on the proof of the cocycle
property. -/
lemma relCocycleOf_irrel {n : ℕ} (a : relKern ℤ X A n) (h₁ h₂ : relDiffLM ℤ X A n a = 0) :
    relCocycleOf ℤ X A a h₁ = relCocycleOf ℤ X A a h₂ := by
  have hinj := (ModuleCat.mono_iff_injective ((relComplex ℤ X A).iCycles n)).mp inferInstance
  exact hinj (by rw [iCycles_relCocycleOf])

/-- The relative cohomology class of a relative cocycle does not depend on the proof of the cocycle
property. -/
lemma relClassOf_congr {n : ℕ} (a : relKern ℤ X A n) (h₁ h₂ : relDiffLM ℤ X A n a = 0) :
    relClassOf ℤ X A a h₁ = relClassOf ℤ X A a h₂ :=
  congrArg (fun z : (relComplex ℤ X A).cycles n => ((relComplex ℤ X A).homologyπ n).hom z)
    (relCocycleOf_irrel a h₁ h₂)

/-- The relative cohomology class commutes with the transport of a relative cocycle along an
equality of degrees. -/
lemma relClassOf_cast {n m : ℕ} (h : n = m) (γ : relKern ℤ X A n)
    (hγ : relDiffLM ℤ X A n γ = 0) :
    relClassOf ℤ X A (h ▸ γ) (relCocycleProof h γ hγ) = h ▸ relClassOf ℤ X A γ hγ := by
  cases h
  exact relClassOf_congr γ _ hγ

/-! ## The chain-level mixed cap/cup identity, in general degrees -/

/-- **The mixed cap/cup identity in general degrees, on the chain level, for a chain whose boundary
is trivial in `C_*(X,A)`.**  For an absolute cocycle `a` of degree `q`, a relative cocycle `u` of
degree `p` and a chain `z` of degree `p+q` with `∂z = 0` in `C_{p+q-1}(X,A)`:

`⟨a, z ⌢ u.1⟩ = (a ⌣ u.1)(z)`

(the right-hand product transported from degree `q+p` to degree `p+q`).  This is the general form of
`Work.Cohomology.kronecker_cap_cup_comm`; the difference between the two orders of the factors is the
coboundary `δ(cup1 …)`, which vanishes on `z` because `cup1 …` is relative and `∂z` is supported in
`A`. -/
lemma kronecker_cap_cup_comm_rel (X : TopCat) (A : Set X) (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : Even (p * q))
    (a : Cochain ℤ (TopCat.toSSet.obj X) q) (ha : cochainDiff ℤ (TopCat.toSSet.obj X) a = 0)
    (u : relKern ℤ X A p) (hu : relDiffLM ℤ X A p u = 0)
    (z : (singularChains ℤ X).X (p + q))
    (hz : relDualProj X A (p + q - 1) (((singularChains ℤ X).d (p + q) (p + q - 1)).hom z) = 0) :
    kronecker ℤ (TopCat.toSSet.obj X) a (cap ℤ (TopCat.toSSet.obj X) u.1 q z)
      = kronecker ℤ (TopCat.toSSet.obj X)
          ((Nat.add_comm q p) ▸ (cup ℤ (TopCat.toSSet.obj X) a u.1)) z := by
  rw [kronecker_cap_cup]
  have hα' : cochainDiff ℤ (TopCat.toSSet.obj X)
      (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) = 0 :=
    relClassOf_cochainDiff ℤ X A u hu
  have hid := cup1Identity ℤ (TopCat.toSSet.obj X) p q hp hq
    (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) a hα' ha
  have hzero : ∀ (h : p + q - 1 + 1 = p + q),
      kronecker ℤ (TopCat.toSSet.obj X)
        (h ▸ (cochainDiff ℤ (TopCat.toSSet.obj X)
          (cup1 ℤ (TopCat.toSSet.obj X) p q
            (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) a))) z = 0 := by
    intro h
    rw [kronecker_cast]
    show (cup1 ℤ (TopCat.toSSet.obj X) p q (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) a)
      (((singularChains ℤ X).d (p + q - 1 + 1) (p + q - 1)).hom (h.symm ▸ z)) = 0
    rw [chain_d_eqRec (singularChains ℤ X) h z]
    exact relKern_apply_eq_zero_of_relDualProj_eq_zero X A
      ⟨cup1 ℤ (TopCat.toSSet.obj X) p q (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) a,
        cup1_mem_relKern_left ℤ X A u.2 a⟩ _ hz
  have h2 := congrArg (fun (γ : Cochain ℤ (TopCat.toSSet.obj X) (p + q)) =>
    kronecker ℤ (TopCat.toSSet.obj X) γ z) hid
  rw [hzero] at h2
  rw [hpq.neg_one_pow, one_smul] at h2
  have h3 : ∀ (α β : Cochain ℤ (TopCat.toSSet.obj X) (p + q)),
      kronecker ℤ (TopCat.toSSet.obj X) (α - β) z
        = kronecker ℤ (TopCat.toSSet.obj X) α z
          - kronecker ℤ (TopCat.toSSet.obj X) β z := fun α β => rfl
  rw [h3] at h2
  linarith [h2]

/-! ## The mixed cap/cup adjunction against the relative Kronecker pairing -/

/-- **The mixed cap/cup adjunction, against the relative Kronecker pairing.**  For a pair `(X,A)`, an
absolute cohomology class `x` of degree `q`, a relative class `β` of degree `p` and a relative
homology class `c` of degree `p+q`:

`⟨x, β ⌢ c⟩ = ⟨x ⌣ β, c⟩`

where the right-hand side is the relative Kronecker pairing `Work.Tubular.relKronH` (the transport
`(Nat.add_comm q p)` makes the degrees agree: `mixedCup` lands in degree `q+p` while `c` lives in
degree `p+q`).  The sign `(-1)^{pq}` is `+1` because `p*q` is even.

This is the corrected form of `Work.Tubular.kronH_mixedCup_relCapPair` promised in `README.md`
§21.1/§22.2: no absolute lift of `c` is needed. -/
theorem kronH_mixedCup_relKronH (X : TopCat) (A : Set X) (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : Even (p * q))
    (x : (singularCochainComplex ℤ X).homology q)
    (beta : (relComplex ℤ X A).homology p)
    (c : (relChains X A).homology (p + q)) :
    kronH ℤ (TopCat.toSSet.obj X) q x (relCapPair X A p q beta c)
      = relKronH X A (p + q) ((Nat.add_comm q p) ▸ (mixedCup X A q p x beta)) c := by
  obtain ⟨a, ha, rfl⟩ := exists_cohomologyClassOf ℤ (TopCat.toSSet.obj X) q x
  obtain ⟨u, hu, rfl⟩ := exists_relClassOf ℤ X A p beta
  obtain ⟨cc, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((relChains X A).homologyπ (p + q))).mp inferInstance c
  -- a lift of the relative cycle to an absolute chain, and its boundary
  obtain ⟨xx, hxx⟩ : ∃ x : (singularChains ℤ X).X (p + q),
      relDualProj X A (p + q) x = ((relChains X A).iCycles (p + q)) cc :=
    relDualProj_surjective X A (p + q) _
  have hstep : (relChains_cokernelIso X A (p + q)).hom (((relChains X A).iCycles (p + q)) cc)
      = (cokernel.π ((inclChains X A).f (p + q))).hom xx := by
    rw [← hxx]
    exact relChains_cokernelIso_canon_apply X A (p + q) xx
  have hx : relDualProj X A (p + q - 1)
      (((singularChains ℤ X).d (p + q) (p + q - 1)).hom xx) = 0 := by
    -- transport the lift to the degree in which the differential is stated
    have hcomm := LinearMap.congr_fun (relDualProj_comm_lm X A (p + q - 1))
      ((Nat.sub_add_cancel (by omega : 1 ≤ p + q)).symm ▸ xx)
    simp only [LinearMap.comp_apply] at hcomm
    rw [chain_d_eqRec (singularChains ℤ X) (Nat.sub_add_cancel (by omega : 1 ≤ p + q)) xx] at hcomm
    rw [← hcomm, ← cast_apply (fun n (z : (singularChains ℤ X).X n) => relDualProj X A n z)
      (Nat.sub_add_cancel (by omega : 1 ≤ p + q)).symm xx, hxx]
    have h := congrArg
      (fun (g : (relChains X A).cycles (p + q) ⟶ (relChains X A).X (p + q - 1)) => g.hom cc)
      (HomologicalComplex.iCycles_d (relChains X A) (p + q) (p + q - 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h
    rw [chain_d_eqRec (relChains X A) (Nat.sub_add_cancel (by omega : 1 ≤ p + q))
      (((relChains X A).iCycles (p + q)) cc)]
    exact h
  -- the left-hand side
  have hLHS : kronH ℤ (TopCat.toSSet.obj X) q
        (cohomologyClassOf ℤ (TopCat.toSSet.obj X) a ha)
        (relCapPair X A p q (relClassOf ℤ X A u hu)
          (((relChains X A).homologyπ (p + q)) cc))
      = kronecker ℤ (TopCat.toSSet.obj X) a (cap ℤ (TopCat.toSSet.obj X) u.1 q xx) := by
    rw [show relClassOf ℤ X A u hu
        = ((relComplex ℤ X A).homologyπ p) (relCocycleOf ℤ X A u hu) from rfl]
    rw [relCapPair_apply X A p q (relCocycleOf ℤ X A u hu) cc]
    rw [kronH_apply_sing X a ha (relCapPairZ X A p q (relCocycleOf ℤ X A u hu) cc)]
    rw [relCapPairZ_iCycles X A p q (relCocycleOf ℤ X A u hu) cc]
    rw [iCycles_relCocycleOf ℤ X A u hu]
    rw [hstep]
    rw [relCapHalf_apply_incl X A (m := q) u xx]
    rfl
  -- the right-hand side
  have hRHS : relKronH X A (p + q)
        ((Nat.add_comm q p) ▸ (mixedCup X A q p
          (cohomologyClassOf ℤ (TopCat.toSSet.obj X) a ha) (relClassOf ℤ X A u hu)))
        (((relChains X A).homologyπ (p + q)) cc)
      = kronecker ℤ (TopCat.toSSet.obj X)
          ((Nat.add_comm q p) ▸ (cup ℤ (TopCat.toSSet.obj X) a u.1)) xx := by
    obtain ⟨hmem, hmem2, hmixed⟩ := mixedCup_apply X A q p a u ha hu
    rw [hmixed]
    rw [← relClassOf_cast (Nat.add_comm q p)
      ⟨cup ℤ (TopCat.toSSet.obj X) a (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p), hmem⟩ hmem2]
    rw [relKronH_apply X A (p + q)
      ((Nat.add_comm q p) ▸ ⟨cup ℤ (TopCat.toSSet.obj X) a
        (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p), hmem⟩) _ cc xx (by rw [hstep])]
    rw [show (((Nat.add_comm q p) ▸ ⟨cup ℤ (TopCat.toSSet.obj X) a
          (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p), hmem⟩ :
            relKern ℤ X A (p + q))).1
        = (Nat.add_comm q p) ▸ (cup ℤ (TopCat.toSSet.obj X) a
            (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p)) from
      (cast_apply (fun n (γ : relKern ℤ X A n) => γ.1) (Nat.add_comm q p) _).symm]
  rw [hLHS, hRHS]
  exact kronecker_cap_cup_comm_rel X A p q hp hq hpq a ha u hu xx hx

end

end Work.Tubular
