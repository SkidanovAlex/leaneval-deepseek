import Mathlib
import Submission.Work.Pi6.SQM.Defs
import Submission.Work.Cohomology.pd_us_cycles_eq_of_class_eq
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.Pi6.SQASM.connHomology
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.Stems.HurewiczMapNatural
import Submission.Work.Cohomology.CompactSupport

/-! Guidance from the project lead (the requester):

SQM assembly. Read REFS/NOTES_LEAD_SQM.md §5 "sqCyclicCoreAsm" (six numbered steps; every input is a hypothesis of
your statement). Build Ωh : C(Path k₀ k₀, Path (h k₀) (h k₀)) as γ ↦ γ.map h.continuous (continuity: Path's topology
is induced from C(I,·); postcomposition is continuous). Loop spaces are range models by Work.Stems.isEMSpaceUpTo_loop.
Hurewicz on ΩK: Work.Stems.hurewicz_first_degree. Cup of classes = class of cup: Work.Cohomology.cupH'_apply.
Do not re-prove any hypothesis. Delegate the small helpers (x∪ᵢx is a cocycle, rank-one uniqueness over 𝔽₂, Ωh).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial unitInterval

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff cohomologyClassOf SSetCochainComplex cocycleOf
  iCycles_cocycleOf SSetCochainComplex_d cochainDiffLM cochainDiffLM_apply homologyπ_eq_zero_of_d
  exists_cohomologyClassOf genEval_ext cupH'_apply cochainDiff_cast eqRec_zero
  eqRec_symm_eqRec_self' singularCohomologyMap_classOf cochainDiff_dualMap_chainComplexMap
  cochainDiff_cup_of_cocycles cohomologyClassOf_congr cup1Identity cochainDiff_cochainDiff)

/-! ## Elementary helpers (characteristic two, rank one, transports, Ω of a map) -/

/-- `a + a = 0` in a module over `𝔽₂`. -/
private lemma add_self_eq_zero_f2 {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (a : M) : a + a = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h : (2 : ZMod 2) • a = 0 := by rw [h2, zero_smul]
  simpa [two_smul] using h

/-- In characteristic two, `a + b = c` gives `a = b + c`. -/
private lemma eq_add_of_add_eq_f2 {M : Type} [AddCommGroup M] [Module (ZMod 2) M] {a b c : M}
    (h : a + b = c) : a = b + c := by
  rw [← h]
  calc a = a + 0 := by rw [add_zero]
    _ = a + (b + b) := by rw [add_self_eq_zero_f2 b]
    _ = b + (a + b) := by abel

/-- A cast along a self-equality of degrees is the identity. -/
private lemma eqRec_self' {α : ℕ → Type*} {a : ℕ} (h : a = a) (x : α a) : h ▸ x = x := by cases h; rfl

/-- A nonzero morphism of modules is nonzero somewhere. -/
private lemma exists_apply_ne_zero {R : Type} [CommRing R] {M N : ModuleCat R} (f : M ⟶ N) (hf : f ≠ 0) :
    ∃ x : ↥M, f x ≠ 0 := by
  by_contra h
  push Not at h
  refine hf (ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  simpa using h x

/-- **Rank one uniqueness over `𝔽₂`**: in a vector space of dimension `≤ 1` over `𝔽₂` any two
nonzero vectors are equal. -/
private lemma eq_of_rank_le_one_f2 {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (h : Module.rank (ZMod 2) M ≤ 1) {x y : M} (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
  haveI : Module.Free (ZMod 2) M := Module.Free.of_divisionRing _ _
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.1 h
  obtain ⟨c, hc⟩ := hv₀ x
  obtain ⟨d, hd⟩ := hv₀ y
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hcd : c = d := by
    rcases h01 c with h0 | h1 <;> rcases h01 d with h0' | h1' <;> simp_all
  rw [← hc, ← hd, hcd]

/-- The map `Ωh : ΩK → ΩL` induced by a continuous map `h : K → L` by postcomposition. -/
private theorem exists_omegaMap {K L : Type} [TopologicalSpace K] [TopologicalSpace L]
    (h : C(K, L)) (k₀ : K) :
    ∃ Ωh : C(Path k₀ k₀, Path (h k₀) (h k₀)), ∀ (γ : Path k₀ k₀) (t : unitInterval),
      Ωh γ t = h (γ t) := by
  refine ⟨⟨fun γ => γ.map h.continuous, ?_⟩, fun γ t => ?_⟩
  · rw [← Path.continuous_uncurry_iff]
    have hfun : (↿fun γ : Path k₀ k₀ => γ.map h.continuous) =
        fun p : Path k₀ k₀ × unitInterval => h (p.1 p.2) := by
      funext p
      exact congrFun (Path.map_coe p.1 h.continuous) p.2
    rw [hfun]
    exact h.continuous.comp ContinuousEval.continuous_eval
  · exact congrFun (Path.map_coe γ h.continuous) t

/-! ## The two directions of "cohomologous = same class" -/

set_option backward.isDefEq.respectTransparency false in  -- v435decl
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in  -- v435decl
set_option backward.isDefEq.respectTransparency.types false in  -- v435decl
/-- Adding a coboundary to a cocycle does not change the cohomology class. -/
private lemma addCoboundaryClassEq {X : SSet} {n : ℕ} (β : Cochain (ZMod 2) X (n + 1))
    (v : Cochain (ZMod 2) X n) (hβ : cochainDiff (ZMod 2) X β = 0)
    (h : cochainDiff (ZMod 2) X (β + cochainDiff (ZMod 2) X v) = 0) :
    cohomologyClassOf (ZMod 2) X (β + cochainDiff (ZMod 2) X v) h =
      cohomologyClassOf (ZMod 2) X β hβ := by
  have hz : ((SSetCochainComplex (ZMod 2) X).iCycles (n + 1))
      (cocycleOf (ZMod 2) X (β + cochainDiff (ZMod 2) X v) h
        - cocycleOf (ZMod 2) X β hβ)
      = ((SSetCochainComplex (ZMod 2) X).d n (n + 1)).hom v := by
    rw [map_sub, iCycles_cocycleOf, iCycles_cocycleOf]
    simp only [SSetCochainComplex_d, cochainDiffLM_apply]
    abel
  have h0 := homologyπ_eq_zero_of_d (ZMod 2) X (n + 1) n
    (cocycleOf (ZMod 2) X (β + cochainDiff (ZMod 2) X v) h
      - cocycleOf (ZMod 2) X β hβ) v hz
  rw [map_sub, sub_eq_zero] at h0
  exact h0

set_option backward.isDefEq.respectTransparency false in  -- v435decl
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in  -- v435decl
set_option backward.isDefEq.respectTransparency.types false in  -- v435decl
/-- If two cocycles have the same cohomology class then they differ by a coboundary. -/
private lemma coboundaryOfClassEq {X : SSet} {n : ℕ} (α β : Cochain (ZMod 2) X (n + 1))
    (hα : cochainDiff (ZMod 2) X α = 0) (hβ : cochainDiff (ZMod 2) X β = 0)
    (h : cohomologyClassOf (ZMod 2) X α hα = cohomologyClassOf (ZMod 2) X β hβ) :
    ∃ v : Cochain (ZMod 2) X n, cochainDiff (ZMod 2) X v = α - β := by
  obtain ⟨v, hv⟩ := Work.Cohomology.pd_us_cycles_eq_of_class_eq
    (K := SSetCochainComplex (ZMod 2) X) (n := n)
    (cocycleOf (ZMod 2) X α hα) (cocycleOf (ZMod 2) X β hβ) h
  refine ⟨(v : Cochain (ZMod 2) X n), ?_⟩
  have h1 : (ModuleCat.Hom.hom ((SSetCochainComplex (ZMod 2) X).d n (n + 1))) v =
      cochainDiff (ZMod 2) X (v : Cochain (ZMod 2) X n) := by
    rw [SSetCochainComplex_d]
    rfl
  have h2 : (ModuleCat.Hom.hom ((SSetCochainComplex (ZMod 2) X).d n (n + 1))) v =
      (α : ↑((SSetCochainComplex (ZMod 2) X).X (n + 1))) -
        (β : ↑((SSetCochainComplex (ZMod 2) X).X (n + 1))) := by
    rw [hv, iCycles_cocycleOf, iCycles_cocycleOf]
    try rfl
  rw [← h1]
  exact h2

/-! ## `x ∪ᵢ x` is a cocycle for a cocycle `x` -/

/-- The `(n+1)`- and `(n+2)`-st terms of the cup-2 formula vanish when an argument is `0`. -/
private lemma cup2_zero_left (X : SSet) (n m : ℕ) (v : Cochain (ZMod 2) X m) :
    Work.Pi6.SQ.cup2 X n m (0 : Cochain (ZMod 2) X n) v = 0 := by
  apply genEval_ext
  intro s
  rw [Work.Pi6.SQ.genEval_cup2]
  simp only [genEval, LinearMap.zero_apply, zero_mul, Finset.sum_const_zero]

private lemma cup2_zero_right (X : SSet) (n m : ℕ) (u : Cochain (ZMod 2) X n) :
    Work.Pi6.SQ.cup2 X n m u (0 : Cochain (ZMod 2) X m) = 0 := by
  apply genEval_ext
  intro s
  rw [Work.Pi6.SQ.genEval_cup2]
  simp only [genEval, LinearMap.zero_apply, mul_zero, Finset.sum_const_zero]

/-- Casts of `0` in the cochain complexes. -/
private lemma eqRec_zero_cochain {X : SSet} {a b : ℕ} (h : a = b) :
    (h ▸ (0 : Cochain (ZMod 2) X a)) = (0 : Cochain (ZMod 2) X b) := by cases h; rfl

/-- Casts along a self-equality of degrees in the cochain complexes. -/
private lemma eqRec_self_cochain {X : SSet} {a : ℕ} (h : a = a) (x : Cochain (ZMod 2) X a) :
    h ▸ x = x := by cases h; rfl

/-- A transport of a cochain whose image is zero is zero. -/
private lemma cochain_eq_zero_of_cast_eq_zero {X : SSet} {p q : ℕ} {h : p = q}
    {x : Cochain (ZMod 2) X p} (hx : h ▸ x = 0) : x = 0 := by
  have hc := congrArg (fun t => h.symm ▸ t) hx
  rwa [eqRec_symm_eqRec_self', eqRec_zero_cochain] at hc

/-- The coboundary is additive. -/
private lemma cochainDiff_add {X : SSet} {n : ℕ} (a b : Cochain (ZMod 2) X n) :
    cochainDiff (ZMod 2) X (a + b) =
      cochainDiff (ZMod 2) X a + cochainDiff (ZMod 2) X b := by
  have h := map_add (cochainDiffLM (ZMod 2) X n) a b
  simpa only [cochainDiffLM_apply] using h

set_option backward.isDefEq.respectTransparency false in  -- v435decl
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in  -- v435decl
set_option backward.isDefEq.respectTransparency.types false in  -- v435decl
/-- `x ∪₁ x` is a cocycle when `x` is (from the library's coboundary formula for `∪₁`). -/
private lemma cocycle_cup1m_self {X : SSet} {n : ℕ} (hn : 1 ≤ n) (x : Cochain (ZMod 2) X n)
    (hx : cochainDiff (ZMod 2) X x = 0) :
    cochainDiff (ZMod 2) X (Work.Pi6.SQ.cup1m X n n x x) = 0 := by
  have hid := cup1Identity (ZMod 2) X n n hn hn x x hx hx
  have hpow : (-1 : ZMod 2) ^ (n * n) = 1 := by
    have h1 : (-1 : ZMod 2) = 1 := by decide
    rw [h1, one_pow]
  have hcast := Nat.sub_add_cancel (by omega : 1 ≤ n + n)
  have h0 : hcast ▸ cochainDiff (ZMod 2) X (Work.Cohomology.cup1 (ZMod 2) X n n x x) = 0 := by
    rw [hid, eqRec_self_cochain (Nat.add_comm n n) (Work.Cohomology.cup (ZMod 2) X x x),
      hpow, one_smul, sub_self]
  have hlib : cochainDiff (ZMod 2) X (Work.Cohomology.cup1 (ZMod 2) X n n x x) = 0 := by
    have hcongr := congrArg (fun t => hcast.symm ▸ t) h0
    rwa [eqRec_symm_eqRec_self', eqRec_zero_cochain] at hcongr
  simpa only [Work.Pi6.SQ.cup1m] using
    (cochainDiff_cast (R := ZMod 2) (X := X)
      (h := congrArg (fun k => k - 1) (Nat.add_comm n n))
      (Work.Cohomology.cup1 (ZMod 2) X n n x x) hlib)

set_option backward.isDefEq.respectTransparency false in  -- v435decl
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in  -- v435decl
set_option backward.isDefEq.respectTransparency.types false in  -- v435decl
/-- `x ∪₂ x` is a cocycle when `x` is (from area SQM's `Cup2Cob`). -/
private lemma cocycle_cup2_self {X : SSet} {n : ℕ} (hn : 1 ≤ n) (x : Cochain (ZMod 2) X n)
    (hx : cochainDiff (ZMod 2) X x = 0) (h2 : Cup2Cob) :
    cochainDiff (ZMod 2) X (Work.Pi6.SQ.cup2 X n n x x) = 0 := by
  have hid := h2 X n n x x hn hn
  have hcast : (n + n - 2) + 1 = n + n - 1 := by omega
  have h0 : hcast ▸ cochainDiff (ZMod 2) X (Work.Pi6.SQ.cup2 X n n x x) = 0 := by
    rw [hid, hx, cup2_zero_left, cup2_zero_right]
    simp only [eqRec_zero_cochain, eqRec_self_cochain, add_zero]
    exact add_self_eq_zero_f2 _
  have hcongr := congrArg (fun t => hcast.symm ▸ t) h0
  rwa [eqRec_symm_eqRec_self', eqRec_zero_cochain] at hcongr

/-! ## Hurewicz inputs for a `K(ℤ/2,2)` model -/

set_option backward.isDefEq.respectTransparency false in  -- v435decl
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in  -- v435decl
set_option backward.isDefEq.respectTransparency.types false in  -- v435decl
/-- For a `K(ℤ/2,2)` range model: `H₁(−;ℤ) = 0` and every element of `H₂(−;ℤ)` has exponent `2`. -/
private theorem hurewiczInputs {X : Type} [TopologicalSpace X] (x₀ : X) (N : ℕ) (hN : 3 ≤ N)
    (hX : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X x₀) :
    Subsingleton (Work.Pi6.HR ℤ X 1) ∧ (∀ a : Work.Pi6.HR ℤ X 2, (2 : ℤ) • a = 0) := by
  have hconn : ∀ j : ℕ, j < 2 → Subsingleton (HomotopyGroup (Fin j) X x₀) :=
    fun j hj => hX.2 j (by omega) (Or.inl hj)
  refine ⟨?_, ?_⟩
  · exact ModuleCat.subsingleton_of_isZero
      (Work.Pi6.SQASM.connHomology x₀ 1 1 (fun j hj => hconn j (by omega)) (by norm_num) le_rfl)
  · intro a
    obtain ⟨w, hw⟩ := (Work.Stems.hurewicz_first_degree (Y := X) 2 (by norm_num) x₀ hconn).2 a
    have hww : w * w = 1 := by
      obtain ⟨e⟩ := hX.1
      refine e.injective ?_
      rw [map_mul, map_one]
      have hz : ∀ z : Multiplicative (ZMod 2), z * z = 1 := by decide
      exact hz (e w)
    rw [← hw]
    have h2s : (2 : ℤ) • Work.Stems.hurewiczMapN 2 (by norm_num) x₀ w =
        Work.Stems.hurewiczMapN 2 (by norm_num) x₀ w +
          Work.Stems.hurewiczMapN 2 (by norm_num) x₀ w := two_zsmul _
    rw [h2s, ← Work.Stems.hurewiczMapN_mul 1 x₀ w w, hww]
    exact Work.Stems.hurewiczMap_one 1


/-! ## The assembly -/

open Work.Cohomology (SSetCochainComplex cocycleOf iCycles_cocycleOf SSetCochainComplex_d
  cochainDiffLM_apply homologyπ_eq_zero_of_d cupH'_apply cochainDiff_cast eqRec_zero
  eqRec_symm_eqRec_self')

set_option backward.isDefEq.respectTransparency false in  -- v435decl
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in  -- v435decl
set_option backward.isDefEq.respectTransparency.types false in  -- v435decl
/-- **SQM assembly (area SQ, crux A)**: `Sq²Sq²ι₃ ≠ 0` from the six cochain-level inputs. -/
theorem sqCyclicCoreAsm (hS : Work.Pi6.SQM.SigmaStar) (hI : Work.Pi6.SQM.SqOneInjective)
    (hO : Work.Pi6.SQM.SqOpsProp) (hC : Work.Pi6.SQM.CartanProp) (hN : Work.Pi6.SQM.CupINatural)
    (h1 : Work.Pi6.SQM.Cup1Cob) (h2 : Work.Pi6.SQM.Cup2Cob) (hM2 : Work.Pi6.EMMod2)
    (hNZ : ∀ (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ), 3 ≤ N →
      Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X x₀ →
      Nontrivial (Work.Pi6.Coh (ZMod 2) X 2)) :
    Work.Pi6.SqCyclicCore := by
  intro K L _ _ k₀ l₀ N hN11 hK hL h hbase h5
  subst hbase
  obtain ⟨sg, hnat, hc1s, hc2s, hc3s, hc4s, hc5s, hrange, hlift⟩ := hS
  -- 0. connectivity of `K` and `L`
  have hconnK : ∀ i : ℕ, i < 3 → Subsingleton (HomotopyGroup (Fin i) K k₀) :=
    fun i hi => hK.2 i (by omega) (Or.inl hi)
  have hconnL : ∀ i : ℕ, i < 5 → Subsingleton (HomotopyGroup (Fin i) L (h k₀)) :=
    fun i hi => hL.2 i (by omega) (Or.inl hi)
  -- 1. `ΩK` is a model of `K(ℤ/2,2)` through `N-1`
  have hloopK : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) (N - 1) (Path k₀ k₀)
      (Path.refl k₀) :=
    Work.Stems.isEMSpaceUpTo_loop (A := ZMod 2) (k := 2) (M := N) (by norm_num) k₀ hK
  haveI hntΩK : Nontrivial (Coh (ZMod 2) (Path k₀ k₀) 2) :=
    hNZ (Path k₀ k₀) (Path.refl k₀) (N - 1) (by omega) hloopK
  obtain ⟨ι₂, hι₂⟩ := exists_ne (0 : Coh (ZMod 2) (Path k₀ k₀) 2)
  obtain ⟨r, hr, hrcls⟩ := exists_cohomologyClassOf (ZMod 2) (SX (Path k₀ k₀)) 2 ι₂
  obtain ⟨hH1, hH2⟩ := hurewiczInputs (Path.refl k₀) (N - 1) (by omega) hloopK
  have hrr1 : cochainDiff (ZMod 2) (SX (Path k₀ k₀))
      (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r) = 0 :=
    cocycle_cup1m_self (by norm_num) r hr
  have hsq1r_ne : cls (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r) hrr1 ≠ 0 := by
    intro h0
    refine hι₂ ?_
    rw [← hrcls]
    exact hI (Path k₀ k₀) hH1 hH2 r hr hrr1 h0
  -- the EMMod2 facts on `ΩK`
  have hM2ΩK := hM2.1 (Path k₀ k₀) (Path.refl k₀) (N - 1) (by omega) hloopK
  have hrr : cochainDiff (ZMod 2) (SX (Path k₀ k₀))
      (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r) = 0 :=
    cochainDiff_cup_of_cocycles (ZMod 2) (SX (Path k₀ k₀)) r r hr hr
  have hC0 : cochainDiff (ZMod 2) (SX (Path k₀ k₀))
      (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀))
        (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r)
        (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r)) = 0 :=
    cochainDiff_cup_of_cocycles (ZMod 2) (SX (Path k₀ k₀)) _ _ hrr1 hrr1
  have hC_ne : cls (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀))
        (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r)
        (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r)) hC0 ≠ 0 := by
    intro h0
    have h1 := cupH'_apply (ZMod 2) (SX (Path k₀ k₀))
      (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r)
      (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r) hrr1 hrr1 hC0
    exact hM2ΩK.2.2 (cls (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r) hrr1) hsq1r_ne
      (h1.trans h0)
  -- 2. `ι₃ ∈ H³(K)` with `σ ι₃ = ι₂`
  have hbij2 : Function.Bijective (sg K k₀ 2) :=
    (hrange K k₀ 3 (by norm_num) hconnK 2 (by omega)).1 (by norm_num)
  let e2 : Coh (ZMod 2) K 3 ≃ₗ[ZMod 2] Coh (ZMod 2) (Path k₀ k₀) 2 :=
    LinearEquiv.ofBijective (sg K k₀ 2) hbij2
  let ι₃ : Coh (ZMod 2) K 3 := e2.symm ι₂
  have hσ2 : sg K k₀ 2 ι₃ = ι₂ := e2.apply_symm_apply ι₂
  obtain ⟨x, hx, hxcls⟩ := exists_cohomologyClassOf (ZMod 2) (SX K) 3 ι₃
  have hxx : cochainDiff (ZMod 2) (SX K) (Work.Pi6.SQ.cup1m (SX K) 3 3 x x) = 0 :=
    cocycle_cup1m_self (by norm_num) x hx
  -- 3. `σ[x ∪₁ x] = [r ∪ r] ≠ 0`, and `h*z = [x ∪₁ x]` by rank one
  have hc1' : sg K k₀ 4 (cls (Work.Pi6.SQ.cup1m (SX K) 3 3 x x) hxx) =
      cls (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r) hrr :=
    hc1s K k₀ x hx hxx r hr hrr (by
      calc cls r hr = ι₂ := hrcls
        _ = sg K k₀ 2 ι₃ := hσ2.symm
        _ = sg K k₀ 2 (cls x hx) := congrArg (sg K k₀ 2) hxcls.symm)
  have hrr_ne : cls (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r) hrr ≠ 0 := by
    intro h0
    refine hM2ΩK.2.1 ι₂ hι₂ ?_
    have h1 := cupH'_apply (ZMod 2) (SX (Path k₀ k₀)) r r hr hr hrr
    rw [hrcls] at h1
    exact h1.trans h0
  have hsq1_ne : cls (Work.Pi6.SQ.cup1m (SX K) 3 3 x x) hxx ≠ 0 := fun h0 =>
    hrr_ne (by rw [← hc1', h0, map_zero])
  obtain ⟨z, hz⟩ : ∃ z : Coh (ZMod 2) L 5, cmap (ZMod 2) h 5 z ≠ 0 :=
    exists_apply_ne_zero (cmap (ZMod 2) h 5) h5
  have hM2K := hM2.2.1 K k₀ N (by omega) hK
  have hc_eq : cmap (ZMod 2) h 5 z = cls (Work.Pi6.SQ.cup1m (SX K) 3 3 x x) hxx :=
    eq_of_rank_le_one_f2 hM2K.2.1 hz hsq1_ne
  have hφc : sg K k₀ 4 (cmap (ZMod 2) h 5 z) =
      cls (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r) hrr := by
    rw [hc_eq, hc1']
  -- 4. Ωh and naturality of the suspension
  obtain ⟨Ωh, hΩh⟩ := exists_omegaMap h k₀
  have hnat' := hnat K L k₀ h Ωh hΩh 4 z
  have hσL : cmap (ZMod 2) Ωh 4 (sg L (h k₀) 4 z) =
      cls (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r) hrr := by
    rw [← hnat', hφc]
  -- 5. the pullback of a representative `w` of `σ_L z`
  obtain ⟨w, hw, hwcls⟩ :=
    exists_cohomologyClassOf (ZMod 2) (SX (Path (h k₀) (h k₀))) 4 (sg L (h k₀) 4 z)
  let fSS : SX (Path k₀ k₀) ⟶ SX (Path (h k₀) (h k₀)) := TopCat.toSSet.map (TopCat.ofHom Ωh)
  let x4 : Cochain (ZMod 2) (SX (Path k₀ k₀)) 4 :=
    (ModuleCat.Hom.hom ((SSet.chainComplexMap fSS (ModuleCat.of (ZMod 2) (ZMod 2))).f 4)).dualMap w
  have hx4 : cochainDiff (ZMod 2) (SX (Path k₀ k₀)) x4 = 0 :=
    cochainDiff_dualMap_chainComplexMap (ZMod 2) fSS w hw
  have hx4cls : cls x4 hx4 =
      cls (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r) hrr := by
    have h1 : cls x4 hx4 = cmap (ZMod 2) Ωh 4 (cls w hw) :=
      (singularCohomologyMap_classOf (ZMod 2) (TopCat.ofHom Ωh) w hw).symm
    have h3 : cmap (ZMod 2) Ωh 4 (cls w hw) = cmap (ZMod 2) Ωh 4 (sg L (h k₀) 4 z) :=
      congrArg (cmap (ZMod 2) Ωh 4) hwcls
    exact h1.trans (h3.trans hσL)
  obtain ⟨v, hv⟩ := coboundaryOfClassEq
    (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) (n := 2) (m := 2) r r)
    x4 hrr hx4 hx4cls.symm
  have hx4v : x4 + cochainDiff (ZMod 2) (SX (Path k₀ k₀)) v =
      Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r := by
    rw [hv]; abel
  -- 6. `SqOpsProp` and Cartan: `[Sq²(x4)] = [Sq¹(r)²] ≠ 0`
  obtain ⟨y6, hy6⟩ := hO.2.2.2 (SX (Path k₀ k₀)) x4 hx4 v
  have hy6' : cochainDiff (ZMod 2) (SX (Path k₀ k₀)) y6 =
      Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4 x4 x4 +
      Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4
        (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r)
        (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r) := by
    rw [hy6, hx4v]
  have hcart := hC (SX (Path k₀ k₀)) r hr
  have hcup2x4x4 : cochainDiff (ZMod 2) (SX (Path k₀ k₀))
      (Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4 x4 x4) = 0 :=
    cocycle_cup2_self (by norm_num) x4 hx4 h2
  have hA : Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4 x4 x4 =
      Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀))
        (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r)
        (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r) +
      cochainDiff (ZMod 2) (SX (Path k₀ k₀))
        (y6 + Work.Pi6.SQ.cartanCochain (SX (Path k₀ k₀)) r) := by
    refine eq_add_of_add_eq_f2 ?_
    have hB : Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4
          (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r)
          (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r) +
        Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4
          (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r)
          (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r) = 0 :=
      add_self_eq_zero_f2 _
    calc Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4 x4 x4 +
          Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀))
            (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r)
            (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r)
        = Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4 x4 x4 +
            (Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4
                (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r)
                (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r) +
              Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4
                (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r)
                (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r)) +
            Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀))
              (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r)
              (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r) := by rw [hB, add_zero]
      _ = (Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4 x4 x4 +
              Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4
                (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r)
                (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r)) +
            (Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4
                (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r)
                (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) r r) +
              Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀))
                (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r)
                (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r)) := by abel
      _ = cochainDiff (ZMod 2) (SX (Path k₀ k₀)) y6 +
            cochainDiff (ZMod 2) (SX (Path k₀ k₀))
              (Work.Pi6.SQ.cartanCochain (SX (Path k₀ k₀)) r) := by rw [hy6', hcart]
      _ = cochainDiff (ZMod 2) (SX (Path k₀ k₀))
            (y6 + Work.Pi6.SQ.cartanCochain (SX (Path k₀ k₀)) r) := by rw [cochainDiff_add]
  have hclsA : cls (Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4 x4 x4) hcup2x4x4 =
      cls (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀))
        (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r)
        (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r)) hC0 :=
    (cohomologyClassOf_congr (ZMod 2) (SX (Path k₀ k₀)) hA _ _).trans
      (addCoboundaryClassEq (Work.Cohomology.cup (ZMod 2) (SX (Path k₀ k₀)) (n := 3) (m := 3)
          (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r)
          (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 r r))
        (y6 + Work.Pi6.SQ.cartanCochain (SX (Path k₀ k₀)) r) hC0
        (by rw [cochainDiff_add, hC0, cochainDiff_cochainDiff, zero_add]))
  have hA_ne : cls (Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4 x4 x4) hcup2x4x4 ≠ 0 :=
    fun h0 => hC_ne (by rw [← hclsA]; exact h0)
  -- 7. pull back to `ΩL`
  have hww : cochainDiff (ZMod 2) (SX (Path (h k₀) (h k₀)))
      (Work.Pi6.SQ.cup2 (SX (Path (h k₀) (h k₀))) 4 4 w w) = 0 :=
    cocycle_cup2_self (by norm_num) w hw h2
  have hCupINat := (hN (SX (Path k₀ k₀)) (SX (Path (h k₀) (h k₀))) fSS 4 4 w w).2.1
  have homega : cmap (ZMod 2) Ωh 6
        (cls (Work.Pi6.SQ.cup2 (SX (Path (h k₀) (h k₀))) 4 4 w w) hww) =
      cls (Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4 x4 x4) hcup2x4x4 :=
    (singularCohomologyMap_classOf (ZMod 2) (TopCat.ofHom Ωh)
      (Work.Pi6.SQ.cup2 (SX (Path (h k₀) (h k₀))) 4 4 w w) hww).trans
      (cohomologyClassOf_congr (ZMod 2) (SX (Path k₀ k₀)) hCupINat.symm _ _)
  have hE'ne : cls (Work.Pi6.SQ.cup2 (SX (Path (h k₀) (h k₀))) 4 4 w w) hww ≠ 0 := by
    intro h0
    exact hA_ne (by rw [← homega, h0, map_zero])
  -- 8. surjectivity of `σ_L` in degree `6` and conclusion
  have hbij6L : Function.Bijective (sg L (h k₀) 6) :=
    (hrange L (h k₀) 5 (by norm_num) hconnL 6 (by omega)).1 (by norm_num)
  obtain ⟨e, he⟩ := hbij6L.2 (cls (Work.Pi6.SQ.cup2 (SX (Path (h k₀) (h k₀))) 4 4 w w) hww)
  have hnat7 := hnat K L k₀ h Ωh hΩh 6 e
  have hne : cmap (ZMod 2) h 7 e ≠ 0 := by
    intro h0
    exact hA_ne (by rw [← homega, ← he, ← hnat7, h0, map_zero])
  intro h0
  refine hne ?_
  simpa using congrArg (fun f => f e) h0

end

end Work.Pi6.SQM
