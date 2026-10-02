import Mathlib
import Submission.Work.StemsB.wangCollarDerivDefs
import Submission.Work.StemsB.collarSigma_cup
import Submission.Work.Cohomology.gradedComm
import Submission.Work.StemsB.collarLambdaOatIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The derivation property of the Wang transgression `θ = ρ ∘ Σ ∘ u`

The collar computation `Work.StemsB.collarSigma_cup` is the derivation property of the collar
transgression coefficient map `Σ`.  Here it is transported to the geometric transgression
`θ = ρ ∘ Σ ∘ u` of `Work.StemsB.wangTheta` (`wangCollarDerivDefs.lean`):

  `θ_{n+n'}(a ⌣ b) = (-1)^{n+b} · a ⌣ θ_{n'}(b) + (-1)^{b(n'+1)} · θ_n(a) ⌣ b`.

The transport uses the facts, all already available, that

* `u = collarLambdaGCoh` is a ring map (`cupNaturalH`) and commutes with degree transports;
* `ρ = rhoCoh = λ_O-pt^*` is a ring map and commutes with degree transports;
* the section of the collar product followed by `λ_G` is `λ_pt` (`collarLambdaPat`), so that
  `ρ ∘ (section)^* ∘ u = ρ ∘ λ_pt^* = id` (`collarLambdaPat_comp_rho`);
* the second term is brought into the order used by the statement with the graded commutativity
  `Work.Cohomology.gradedComm`; the two signs agree because
  `(n+b)(n'+b) + (n'+b) + (n+1)(n'+b) ≡ b(n'+1) (mod 2)`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.StemsB

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-! ## `transT`: the degree transport of `Work.StemsB.collarCupDefs`

`transT Y h` is the isomorphism `H^k(Y) ≅ H^l(Y)` given by an equality `h : k = l` of degrees.
The lemmas of this section are the (public) copies of the private ones of
`Submission/Work/StemsB/collarSigma_cup.lean`. -/

private lemma transT_eq_eqToHom {Y : Type} [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (v : Work.Thom.Coh ℤ i Y) :
    transT Y h v = (CategoryTheory.eqToHom (congrArg (fun t =>
      (Work.Cohomology.singularCochainComplex ℤ (TopCat.of Y)).homology t) h) :
        Work.Thom.Coh ℤ i Y ⟶ Work.Thom.Coh ℤ j Y) v := by
  cases h; rfl

private lemma CohMap_eqToHom_homology {X' Y' : Type} [TopologicalSpace X']
    [TopologicalSpace Y'] (f : C(X', Y')) {i j : ℕ} (h : i = j)
    (z : (Work.Cohomology.singularCochainComplex ℤ (TopCat.of Y')).homology i) :
    (Work.Thom.CohMap f ℤ j).hom
        (CategoryTheory.eqToHom (congrArg (fun t =>
          (Work.Cohomology.singularCochainComplex ℤ (TopCat.of Y')).homology t) h) z)
      = CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℤ t X') h)
          ((Work.Thom.CohMap f ℤ i).hom z) := by
  cases h; rfl

/-- `transT` is additive. -/
lemma transT_add {Y : Type} [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (v w : Work.Thom.Coh ℤ i Y) : transT Y h (v + w) = transT Y h v + transT Y h w := by
  rw [map_add]

/-- `transT` is `ℤ`-linear. -/
lemma transT_zsmul {Y : Type} [TopologicalSpace Y] {i j : ℕ} (h : i = j) (c : ℤ)
    (v : Work.Thom.Coh ℤ i Y) : transT Y h (c • v) = c • transT Y h v := by
  rw [map_zsmul]

/-- `transT` composes. -/
lemma transT_comp {Y : Type} [TopologicalSpace Y] {k l j : ℕ} (h : k = l) (h' : l = j)
    (v : Work.Thom.Coh ℤ k Y) : transT Y h' (transT Y h v) = transT Y (h.trans h') v := by
  cases h; cases h'; rfl

/-- `transT` is proof-irrelevant in the degree equality. -/
lemma transT_congr {Y : Type} [TopologicalSpace Y] {k l : ℕ} (h h' : k = l)
    (v : Work.Thom.Coh ℤ k Y) : transT Y h v = transT Y h' v := by
  rw [Subsingleton.elim h h']

/-- `transT` along a self-equality is the identity. -/
lemma transT_self {Y : Type} [TopologicalSpace Y] {k : ℕ} (h : k = k)
    (v : Work.Thom.Coh ℤ k Y) : transT Y h v = v := by
  rw [transT_congr h rfl]; rfl

/-- **The round trip:** transporting a class out and back along an equality of degrees is the
identity. -/
lemma transT_round {Y : Type} [TopologicalSpace Y] {k j : ℕ} (h : j = k)
    (Z : Work.Thom.Coh ℤ j Y) : Z = transT Y h.symm (transT Y h Z) :=
  ((transT_comp h h.symm Z).trans (transT_self (h.trans h.symm) Z)).symm

/-- `transT` is a `▸`-cast. -/
lemma transT_cast {Y : Type} [TopologicalSpace Y] {i j : ℕ} (h : i = j)
    (v : Work.Thom.Coh ℤ i Y) : transT Y h v = h ▸ v := by
  rw [transT_eq_eqToHom]; cases h; rfl

/-- The pullback along a continuous map commutes with degree transports. -/
lemma CohMap_transT {X' Y' : Type} [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X', Y')) {i j : ℕ} (h : i = j) (z : Work.Thom.Coh ℤ i Y') :
    (Work.Thom.CohMap f ℤ j).hom (transT Y' h z)
      = transT X' h ((Work.Thom.CohMap f ℤ i).hom z) := by
  rw [transT_eq_eqToHom, transT_eq_eqToHom]
  exact CohMap_eqToHom_homology f h z

/-- `(-1)^a = (-1)^b` for exponents congruent modulo `2`. -/
lemma neg_one_pow_congr_mod {a b : ℕ} (h : a % 2 = b % 2) :
    (-1 : ℤ) ^ a = (-1 : ℤ) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two a, neg_one_pow_eq_pow_mod_two b, h]

/-- **Graded commutativity, in the `transT` spelling**: transporting `x ⌣ y` to the degree of
`y ⌣ x` and swapping the two factors introduces the Koszul sign `(-1)^{|x||y|}`. -/
lemma cupT_swap_transT {Y : Type} [TopologicalSpace Y] (p q : ℕ)
    (x : Work.Thom.Coh ℤ p Y) (y : Work.Thom.Coh ℤ q Y)
    {j : ℕ} (h : p + q = j) (h' : q + p = j) :
    transT Y h (cupT Y p q x y) = (-1 : ℤ)^(p*q) • transT Y h' (cupT Y q p y x) := by
  have hc : h = (Nat.add_comm p q).trans h' := Subsingleton.elim _ _
  rw [hc, ← transT_comp (Nat.add_comm p q) h' (cupT Y p q x y)]
  rw [transT_cast (Nat.add_comm p q) (cupT Y p q x y)]
  rw [show (Nat.add_comm p q) ▸ cupT Y p q x y = (-1 : ℤ)^(p*q) • cupT Y q p y x from by
    rw [← Int.cast_smul_eq_zsmul ℤ ((-1 : ℤ)^(p*q)) (cupT Y q p y x)]
    exact Work.Cohomology.gradedComm ℤ (TopCat.toSSet.obj (TopCat.of Y)) p q x y]
  rw [transT_zsmul]

/-! ## The three maps `u`, `ρ`, the collar section and the collar transgression

Everything here is stated with the fibre `p ⁻¹' {∞}` written as `↥(p ⁻¹' {OnePoint.infty})`, the
spelling in which the definitions of `Work.StemsB.wangTheta` and `Work.StemsB.wangCohFsp` are
elaborated. -/

/-- The pullback along the clutching map commutes with degree transports. -/
lemma GCoh_transT (b : ℕ) (hb1 : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    {i j : ℕ} (h : i = j) (z : Work.Thom.Coh ℤ i ↥(p ⁻¹' {OnePoint.infty})) :
    (collarLambdaGCoh b p d_G hT_G hT_O j).hom (transT ↥(p ⁻¹' {OnePoint.infty}) h z)
      = transT ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1})) h
          ((collarLambdaGCoh b p d_G hT_G hT_O i).hom z) := by
  exact CohMap_transT (collarLambdaG b p d_G hT_G hT_O) h z

/-- The pullback along the clutching map is a ring map. -/
lemma GCoh_cup (b : ℕ) (hb1 : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (m m' : ℕ)
    (x : Work.Thom.Coh ℤ m ↥(p ⁻¹' {OnePoint.infty}))
    (y : Work.Thom.Coh ℤ m' ↥(p ⁻¹' {OnePoint.infty})) :
    (collarLambdaGCoh b p d_G hT_G hT_O (m + m')).hom
        (cupT ↥(p ⁻¹' {OnePoint.infty}) m m' x y)
      = cupT ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1})) m m'
          ((collarLambdaGCoh b p d_G hT_G hT_O m).hom x)
          ((collarLambdaGCoh b p d_G hT_G hT_O m').hom y) := by
  exact Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom (collarLambdaG b p d_G hT_G hT_O)) m m' x y

/-- The section of the collar product followed by `λ_G` is `λ_pt` (as morphisms of cohomology). -/
lemma GCoh_sec_mor (b : ℕ) (hb1 : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ) :
    collarLambdaGCoh b p d_G hT_G hT_O k
      ≫ Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥(p ⁻¹' {d_G.1}))
          (TopCat.of ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1})))
          (TopCat.ofHom (collarSection (Y := ↥(p ⁻¹' {d_G.1})) b hb1)) k
    = lamPtCoh b hb1 p d_G hT_G hT_O k := by
  simp only [collarLambdaGCoh, lamPtCoh]
  rw [← Work.Cohomology.singularCohomologyMap_comp]
  rfl

/-- The section of the collar product followed by `λ_G` is `λ_pt`. -/
lemma GCoh_sec (b : ℕ) (hb1 : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ)
    (x : Work.Thom.Coh ℤ k ↥(p ⁻¹' {OnePoint.infty})) :
    (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥(p ⁻¹' {d_G.1}))
        (TopCat.of ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1})))
        (TopCat.ofHom (collarSection (Y := ↥(p ⁻¹' {d_G.1})) b hb1)) k).hom
        ((collarLambdaGCoh b p d_G hT_G hT_O k).hom x)
      = (lamPtCoh b hb1 p d_G hT_G hT_O k).hom x := by
  exact congrArg (fun φ => φ.hom x) (GCoh_sec_mor b hb1 p d_G hT_G hT_O k)

/-- `ρ ∘ λ_pt^* = id`. -/
lemma rho_lam (b : ℕ) (hb1 : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (k : ℕ)
    (x : Work.Thom.Coh ℤ k ↥(p ⁻¹' {OnePoint.infty})) :
    (rhoCoh b hb1 p d_G hT_G hT_O k).hom ((lamPtCoh b hb1 p d_G hT_G hT_O k).hom x) = x :=
  (collarLambdaPat_comp_rho b hb1 p d_G hT_G hT_O k).1 x

/-- `ρ` is a ring map. -/
lemma rho_cup (b : ℕ) (hb1 : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (m m' : ℕ)
    (x : Work.Thom.Coh ℤ m ↥(p ⁻¹' {d_G.1}))
    (y : Work.Thom.Coh ℤ m' ↥(p ⁻¹' {d_G.1})) :
    (rhoCoh b hb1 p d_G hT_G hT_O (m + m')).hom (cupT ↥(p ⁻¹' {d_G.1}) m m' x y)
      = cupT ↥(p ⁻¹' {OnePoint.infty}) m m'
          ((rhoCoh b hb1 p d_G hT_G hT_O m).hom x)
          ((rhoCoh b hb1 p d_G hT_G hT_O m').hom y) := by
  exact Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom (collarLambdaOat b hb1 p d_G hT_G hT_O))
    m m' x y

/-- `ρ` commutes with degree transports. -/
lemma rho_transT (b : ℕ) (hb1 : 1 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    {i j : ℕ} (h : i = j) (z : Work.Thom.Coh ℤ i ↥(p ⁻¹' {d_G.1})) :
    (rhoCoh b hb1 p d_G hT_G hT_O j).hom (transT ↥(p ⁻¹' {d_G.1}) h z)
      = transT ↥(p ⁻¹' {OnePoint.infty}) h ((rhoCoh b hb1 p d_G hT_G hT_O i).hom z) := by
  exact CohMap_transT (collarLambdaOat b hb1 p d_G hT_G hT_O) h z

/-- **The derivation property of the collar transgression, transported to the fibres**: the
transgression `θ = ρ ∘ Σ ∘ u` is a derivation. -/
theorem derivation_core (b : ℕ) (hb : 2 ≤ b) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (n n' : ℕ) (x : Work.Thom.Coh ℤ (n + b) ↥(p ⁻¹' {OnePoint.infty}))
    (y : Work.Thom.Coh ℤ (n' + b) ↥(p ⁻¹' {OnePoint.infty})) :
    (rhoCoh b (by omega) p d_G hT_G hT_O (n + n' + b + 1)).hom
        (collarSigma b (by omega) (Y := ↥(p ⁻¹' {d_G.1})) (wangSusT b hb ↥(p ⁻¹' {d_G.1}))
          (wangSusT_thom b hb ↥(p ⁻¹' {d_G.1})) (n + n' + b)
          (transT ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1})) (by omega)
            (cupT ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1})) (n + b) (n' + b)
              ((collarLambdaGCoh b p d_G hT_G hT_O (n + b)).hom x)
              ((collarLambdaGCoh b p d_G hT_G hT_O (n' + b)).hom y))))
      = (-1 : ℤ) ^ (n + b) •
          transT ↥(p ⁻¹' {OnePoint.infty}) (by omega)
            (cupT ↥(p ⁻¹' {OnePoint.infty}) (n + b) (n' + 1) x
              (wangTheta b hb p d_G hT_G hT_O n' y))
        + (-1 : ℤ) ^ (b * (n' + 1)) •
          transT ↥(p ⁻¹' {OnePoint.infty}) (by omega)
            (cupT ↥(p ⁻¹' {OnePoint.infty}) (n + 1) (n' + b)
              (wangTheta b hb p d_G hT_G hT_O n x) y) := by
  have hb1 : 1 ≤ b := by omega
  have h1 : (n + b) + (n' + b) = (n + n' + b) + b := by omega
  have h2 : n + n' + b + 1 = (n + b) + (n' + 1) := by omega
  have h3 : (n' + b) + (n + 1) = (n + b) + (n' + 1) := by omega
  have h4 : (n + 1) + (n' + b) = (n + n' + b) + 1 := by omega
  have hcore := collarSigma_cup b hb (Y := ↥(p ⁻¹' {d_G.1})) (wangSusT b hb ↥(p ⁻¹' {d_G.1}))
      (wangSusT_thom b hb ↥(p ⁻¹' {d_G.1})) (wangSusS b hb ↥(p ⁻¹' {d_G.1}))
      (wangSusS_trans b hb ↥(p ⁻¹' {d_G.1})) (wangSusS_sq b hb ↥(p ⁻¹' {d_G.1}))
      (wangSusS_sect b hb ↥(p ⁻¹' {d_G.1})) n n'
      ((collarLambdaGCoh b p d_G hT_G hT_O (n + b)).hom x)
      ((collarLambdaGCoh b p d_G hT_G hT_O (n' + b)).hom y)
  have hrt : collarSigma b hb1 (Y := ↥(p ⁻¹' {d_G.1})) (wangSusT b hb ↥(p ⁻¹' {d_G.1}))
        (wangSusT_thom b hb ↥(p ⁻¹' {d_G.1})) (n + n' + b)
        (transT ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1})) h1
          (cupT ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1})) (n + b) (n' + b)
            ((collarLambdaGCoh b p d_G hT_G hT_O (n + b)).hom x)
            ((collarLambdaGCoh b p d_G hT_G hT_O (n' + b)).hom y)))
      = transT ↥(p ⁻¹' {d_G.1}) h2.symm (transT ↥(p ⁻¹' {d_G.1}) h2
          (collarSigma b hb1 (Y := ↥(p ⁻¹' {d_G.1})) (wangSusT b hb ↥(p ⁻¹' {d_G.1}))
            (wangSusT_thom b hb ↥(p ⁻¹' {d_G.1})) (n + n' + b)
            (transT ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1})) h1
              (cupT ↥(sphLoopCollarProd b ↥(p ⁻¹' {d_G.1})) (n + b) (n' + b)
                ((collarLambdaGCoh b p d_G hT_G hT_O (n + b)).hom x)
                ((collarLambdaGCoh b p d_G hT_G hT_O (n' + b)).hom y))))) :=
    transT_round h2 _
  rw [hrt, rho_transT, hcore]
  rw [map_add, map_zsmul, map_zsmul, transT_add, transT_zsmul, transT_zsmul]
  rw [rho_transT]
  rw [rho_cup, rho_cup]
  rw [GCoh_sec, GCoh_sec]
  rw [rho_lam, rho_lam]
  rw [← wangTheta_apply, ← wangTheta_apply]
  rw [transT_comp h3 h2.symm]
  rw [cupT_swap_transT (n' + b) (n + 1) y (wangTheta b hb p d_G hT_G hT_O n x)
      (h3.trans h2.symm) h4]
  rw [← smul_assoc]
  have hmod : ((n + b) * (n' + b) + (n' + b) + (n' + b) * (n + 1)) % 2 = (b * (n' + 1)) % 2 := by
    obtain ⟨k, hk⟩ := Nat.even_mul_succ_self b
    have hpoly : (n + b) * (n' + b) + (n' + b) + (n' + b) * (n + 1)
        = b * (n' + 1) + 2 * (n * n' + n' + b * n) + (k + k) := by
      rw [← hk]; ring
    omega
  have hcoef : ((-1 : ℤ) ^ ((n + b) * (n' + b) + (n' + b)))
      • ((-1 : ℤ) ^ ((n' + b) * (n + 1))) = (-1 : ℤ) ^ (b * (n' + 1)) := by
    show (-1 : ℤ) ^ ((n + b) * (n' + b) + (n' + b)) * (-1 : ℤ) ^ ((n' + b) * (n + 1))
      = (-1 : ℤ) ^ (b * (n' + 1))
    rw [← pow_add, neg_one_pow_congr_mod hmod]
  rw [hcoef]

theorem wangTheta_cup (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b)) (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G)
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b)
      (Work.StemsB.dOuter b)) :
    ∀ (n n' : ℕ) (a : Work.Cohomology.singularCohomology ℤ (n + b) (Work.StemsB.wangCohFsp b p))
      (b' : Work.Cohomology.singularCohomology ℤ (n' + b) (Work.StemsB.wangCohFsp b p)),
      Work.StemsB.wangTheta b hb p d_G hT_G hT_O (n + n' + b)
          (Work.StemsB.transT ↥(Work.StemsB.wangCohFsp b p) (by omega)
            (Work.StemsB.cupT ↥(Work.StemsB.wangCohFsp b p) (n + b) (n' + b) a b'))
        = (-1 : ℤ) ^ (n + b) •
            Work.StemsB.transT ↥(Work.StemsB.wangCohFsp b p) (by omega)
              (Work.StemsB.cupT ↥(Work.StemsB.wangCohFsp b p) (n + b) (n' + 1) a
                (Work.StemsB.wangTheta b hb p d_G hT_G hT_O n' b'))
          + (-1 : ℤ) ^ (b * (n' + 1)) •
            Work.StemsB.transT ↥(Work.StemsB.wangCohFsp b p) (by omega)
              (Work.StemsB.cupT ↥(Work.StemsB.wangCohFsp b p) (n + 1) (n' + b)
                (Work.StemsB.wangTheta b hb p d_G hT_G hT_O n a) b') := by
  intro n n' a b'
  have hb1 : 1 ≤ b := by omega
  have h1 : (n + b) + (n' + b) = (n + n' + b) + b := by omega
  rw [wangTheta_apply]
  rw [GCoh_transT b hb1 p d_G hT_G hT_O h1
    (cupT ↥(p ⁻¹' {OnePoint.infty}) (n + b) (n' + b) a b')]
  rw [GCoh_cup b hb1 p d_G hT_G hT_O (n + b) (n' + b) a b']
  rw [derivation_core b hb p d_G hT_G hT_O n n' a b']

end

end Work.StemsB
