import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotK.LinkCertGen
import Submission.Work.MotK.KleinTwI5
import Submission.Work.MotK.KleinData
import Submission.Work.MotC2.Relations
import Submission.Work.MotTDG.Defs
import Submission.Work.MotTDG.tenMon_linearIndependent
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

/-!
# `Work.MotK.TwRuling.KleinNondeg`

For a good Klein datum `D` over a field `K`, the quadratic form
`2 a κ₀² − b κ₁ κ₄ ∈ K̄(E)` does not vanish.

The proof is the linear-algebra argument of `TwRuling/GUIDE_KleinNondeg.md`:

* `kPhi` is the `L`-linear map `(Fin 15 → L) →ₗ[L] L(E)` sending a symmetric coefficient
  vector `c` to `∑_{i ≤ j} c_{ij} κ_i κ_j`; its range is the "quadratic span" of the Klein
  coordinates.
* the ten monomials `tenMon` of `L(10·O)` are `L`-independent (`Work.MotTDG.tenMon_linearIndependent`)
  and lie in that span, so the range has dimension `≥ 10`;
* the five Pfaffian quadrics `kleinP a b κ` give five independent relations `lamVec k ∈ ker kPhi`,
  so the kernel has dimension `≥ 5`; rank--nullity then forces `finrank range = 10` and
  `finrank ker = 5`, hence `ker kPhi = span{lamVec k}`;
* the specific vector `cVec` `(2a, 0, …, 0, −b, …)` is not in that span, by the linear functional
  `psi v = v 10 + (a²/b²) · v 8` (it kills all five `lamVec` and takes value `−a²/b ≠ 0` on `cVec`);
* hence `kPhi cVec = 2a κ₀² − b κ₁κ₄ ≠ 0`.

The statement `KleinNondeg` is the specialisation `L = K̄ = AlgebraicClosure K`, using the fields
`klein_eq`, `spans` and `ab_ne` of `D.Good`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine
open scoped BigOperators

namespace Work.MotK.TwRuling

/-! ## §1 The quadratic monomials of `L(10·O)` and the Pfaffian relations -/

/-- The fifteen exponent pairs `(i, j)` with `i ≤ j`, enumerated as
`(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)`. -/
def idxPair : Fin 15 → Fin 5 × Fin 5 :=
  ![((0 : Fin 5), (0 : Fin 5)), ((0 : Fin 5), (1 : Fin 5)), ((0 : Fin 5), (2 : Fin 5)),
    ((0 : Fin 5), (3 : Fin 5)), ((0 : Fin 5), (4 : Fin 5)),
    ((1 : Fin 5), (1 : Fin 5)), ((1 : Fin 5), (2 : Fin 5)), ((1 : Fin 5), (3 : Fin 5)),
    ((1 : Fin 5), (4 : Fin 5)),
    ((2 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (3 : Fin 5)), ((2 : Fin 5), (4 : Fin 5)),
    ((3 : Fin 5), (3 : Fin 5)), ((3 : Fin 5), (4 : Fin 5)),
    ((4 : Fin 5), (4 : Fin 5))]

/-- `idxPair` hits every pair `(i, j)` with `i ≤ j`. -/
theorem idxPair_surj : ∀ q : Fin 5 × Fin 5, q.1 ≤ q.2 → ∃ t : Fin 15, idxPair t = q := by decide

/-- For `k : Fin 5`, the three index-pairs of the support of the Pfaffian `p_k`:
the `-ab`-monomial, the `a²`-monomial and the `-b²`-monomial. -/
def lamIdx : Fin 5 → Fin 15 × Fin 15 × Fin 15 :=
  ![((0 : Fin 15), (10 : Fin 15), (8 : Fin 15)),
    ((9 : Fin 15), (4 : Fin 15), (7 : Fin 15)),
    ((14 : Fin 15), (6 : Fin 15), (3 : Fin 15)),
    ((5 : Fin 15), (13 : Fin 15), (2 : Fin 15)),
    ((12 : Fin 15), (1 : Fin 15), (11 : Fin 15))]

/-- The `-ab`-entry of the `k`-th Pfaffian relation; used to isolate the five relations. -/
def lamDiag : Fin 5 → Fin 15 := ![(0 : Fin 15), 9, 14, 5, 12]

/-- The coefficient vector of the `k`-th Pfaffian quadric `p_k` with respect to the fifteen
products `κ_i κ_j`, `i ≤ j`. -/
noncomputable def lamVec {L : Type*} [CommRing L] (a b : L) (k : Fin 5) : Fin 15 → L :=
  (-(a * b)) • Pi.single ((lamIdx k).1) (1 : L) + (a ^ 2) • Pi.single ((lamIdx k).2.1) (1 : L)
    + (-(b ^ 2)) • Pi.single ((lamIdx k).2.2) (1 : L)

/-- The coefficient vector of the quadric `2a x₀² − b x₁x₄`. -/
noncomputable def cVec {L : Type*} [CommRing L] (a b : L) : Fin 15 → L :=
  (a + a) • Pi.single (0 : Fin 15) (1 : L) + (-b) • Pi.single (8 : Fin 15) (1 : L)

/-- The linear functional `v ↦ v 10 + (a²/b²)·v 8`, which annihilates all the `lamVec a b k`
but not `cVec a b`. -/
noncomputable def psi {L : Type*} [Field L] (a b : L) : (Fin 15 → L) →ₗ[L] L :=
  LinearMap.proj (10 : Fin 15) + (a ^ 2 / b ^ 2) • LinearMap.proj (8 : Fin 15)

lemma lamVec_apply_self {L : Type*} [CommRing L] (a b : L) (k : Fin 5) :
    lamVec a b k (lamDiag k) = -(a * b) := by
  fin_cases k <;> simp [lamVec, lamIdx, lamDiag, Pi.single, Fin.ext_iff]

lemma lamVec_apply_ne {L : Type*} [CommRing L] (a b : L) {k k' : Fin 5} (h : k' ≠ k) :
    lamVec a b k (lamDiag k') = 0 := by
  fin_cases k <;> fin_cases k' <;> simp_all [lamVec, lamIdx, lamDiag, Pi.single]

/-- The five Pfaffian relations are linearly independent coefficient vectors. -/
lemma lamVec_linearIndependent {L : Type*} [Field L] (a b : L) (hab : a * b ≠ 0) :
    LinearIndependent L (lamVec a b) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : ∀ k : Fin 5, c k * (-(a * b)) = 0 := by
    intro k
    have h := congrFun hc (lamDiag k)
    simp only [Finset.sum_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Finset.sum_eq_single k] at h
    · simpa [lamVec_apply_self] using h
    · intro k' _ hk'; rw [lamVec_apply_ne a b (Ne.symm hk'), mul_zero]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  intro k
  exact (mul_eq_zero.mp (key k)).resolve_right (neg_ne_zero.mpr hab)

lemma psi_lamVec {L : Type*} [Field L] (a b : L) (hb : b ≠ 0) (k : Fin 5) :
    psi a b (lamVec a b k) = 0 := by
  fin_cases k <;>
    simp only [psi, lamVec, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
    simp [lamIdx, Fin.ext_iff] <;>
    field_simp <;> ring

lemma psi_cVec {L : Type*} [Field L] (a b : L) (hb : b ≠ 0) :
    psi a b (cVec a b) = -(a ^ 2) / b := by
  simp only [psi, cVec, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp [Fin.ext_iff]
  field_simp <;> ring

/-! ## §2 The quadratic-span map `kPhi` -/

section Main

variable {𝕜 : Type*} [Field 𝕜]
variable (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]

local notation "FF" => FunctionField (D.E.baseChange L)

/-- The `L`-linear map sending a symmetric coefficient vector `c` to `∑_{i ≤ j} c_{ij} κ_i κ_j`,
where `κ = kleinCoord D L`.  Its range is the quadratic span of the Klein coordinates and its
kernel is the space of quadratic relations among them. -/
noncomputable def kPhi : (Fin 15 → L) →ₗ[L] FF where
  toFun c := ∑ t : Fin 15, c t •
    (Work.MotV.kleinCoord D L (idxPair t).1 * Work.MotV.kleinCoord D L (idxPair t).2)
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum, RingHom.id_apply]

lemma kPhi_single (t : Fin 15) :
    kPhi D L (Pi.single t (1 : L)) =
      Work.MotV.kleinCoord D L (idxPair t).1 * Work.MotV.kleinCoord D L (idxPair t).2 := by
  show (∑ t' : Fin 15, (Pi.single t (1 : L) : Fin 15 → L) t' •
    (Work.MotV.kleinCoord D L (idxPair t').1 * Work.MotV.kleinCoord D L (idxPair t').2)) = _
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb; simp [Pi.single, Function.update, hb]
  · intro h; exact absurd (Finset.mem_univ t) h

/-- The range of `kPhi` is the span of all products `κ_i κ_j`. -/
lemma kPhi_range :
    (kPhi D L).range = Submodule.span L (Set.range (fun q : Fin 5 × Fin 5 =>
      Work.MotV.kleinCoord D L q.1 * Work.MotV.kleinCoord D L q.2)) := by
  apply le_antisymm
  · rintro x ⟨c, rfl⟩
    change (∑ t : Fin 15, c t •
      (Work.MotV.kleinCoord D L (idxPair t).1 * Work.MotV.kleinCoord D L (idxPair t).2)) ∈ _
    exact Submodule.sum_mem _ fun t _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨idxPair t, rfl⟩)
  · rw [Submodule.span_le]
    rintro x ⟨q, rfl⟩
    by_cases hq : q.1 ≤ q.2
    · obtain ⟨t, ht⟩ := idxPair_surj q hq
      refine ⟨Pi.single t (1 : L), ?_⟩
      rw [kPhi_single, ht]
    · have hq' : q.2 ≤ q.1 := le_of_lt (not_le.mp hq)
      obtain ⟨t, ht⟩ := idxPair_surj (q.2, q.1) hq'
      refine ⟨Pi.single t (1 : L), ?_⟩
      rw [kPhi_single, ht, mul_comm]

lemma pair_mem_range (i j : Fin 5) :
    Work.MotV.kleinCoord D L i * Work.MotV.kleinCoord D L j ∈ (kPhi D L).range := by
  by_cases h : i ≤ j
  · obtain ⟨t, ht⟩ := idxPair_surj (i, j) h
    refine ⟨Pi.single t (1 : L), ?_⟩
    rw [kPhi_single, ht]
  · have h' : j ≤ i := le_of_lt (not_le.mp h)
    obtain ⟨t, ht⟩ := idxPair_surj (j, i) h'
    refine ⟨Pi.single t (1 : L), ?_⟩
    rw [kPhi_single, ht, mul_comm]

/-- Each of the ten monomials of `L(10·O)` is a product of two elements of the Klein basis. -/
lemma tenMon_eq_prod (t : Fin 10) :
    ∃ a b : Fin 5, Work.MotTDG.tenMon (D.E.baseChange L) t
      = Work.MotTDG.basE (D.E.baseChange L) a * Work.MotTDG.basE (D.E.baseChange L) b := by
  fin_cases t
  · exact ⟨0, 0, by simp [Work.MotTDG.tenMon, Work.MotTDG.goodMon, Work.MotTDG.basE, pow_two]⟩
  · exact ⟨0, 1, by simp [Work.MotTDG.tenMon, Work.MotTDG.goodMon, Work.MotTDG.basE, pow_two]⟩
  · exact ⟨0, 2, by simp [Work.MotTDG.tenMon, Work.MotTDG.goodMon, Work.MotTDG.basE, pow_two]⟩
  · exact ⟨0, 3, by simp [Work.MotTDG.tenMon, Work.MotTDG.goodMon, Work.MotTDG.basE, pow_two]⟩
  · exact ⟨0, 4, by simp [Work.MotTDG.tenMon, Work.MotTDG.goodMon, Work.MotTDG.basE, pow_two]⟩
  · exact ⟨1, 3, by simp [Work.MotTDG.tenMon, Work.MotTDG.goodMon, Work.MotTDG.basE, pow_two]⟩
  · exact ⟨1, 4, by simp [Work.MotTDG.tenMon, Work.MotTDG.goodMon, Work.MotTDG.basE, pow_two]⟩
  · exact ⟨3, 3, by simp [Work.MotTDG.tenMon, Work.MotTDG.goodMon, Work.MotTDG.basE, pow_two]⟩
  · exact ⟨3, 4, by simp [Work.MotTDG.tenMon, Work.MotTDG.goodMon, Work.MotTDG.basE, pow_two]⟩
  · exact ⟨4, 4, by simp [Work.MotTDG.tenMon, Work.MotTDG.goodMon, Work.MotTDG.basE, pow_two]⟩

/-- Inside the range of `kPhi` there also lie all the products of two elements of the Klein
basis, because `spans` expresses the basis in terms of the `κ_i`. -/
lemma tenMon_mem_range (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m : Fin 5, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L FF (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (t : Fin 10) : Work.MotTDG.tenMon (D.E.baseChange L) t ∈ (kPhi D L).range := by
  obtain ⟨x, y, hxy⟩ := tenMon_eq_prod D L t
  rw [hxy]
  have key : ∀ x y : Fin 5, Work.MotTDG.basE (D.E.baseChange L) x
      * Work.MotTDG.basE (D.E.baseChange L) y ∈ (kPhi D L).range := by
    intro x y
    have ex := he x
    have ey := he y
    change Work.MotTDG.basE (D.E.baseChange L) x = _ at ex
    change Work.MotTDG.basE (D.E.baseChange L) y = _ at ey
    rw [ex, ey, Finset.sum_mul_sum]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    rw [show (algebraMap L FF (algebraMap 𝕜 L (e x i)) * Work.MotV.kleinCoord D L i) *
          (algebraMap L FF (algebraMap 𝕜 L (e y j)) * Work.MotV.kleinCoord D L j)
        = (algebraMap 𝕜 L (e x i) * algebraMap 𝕜 L (e y j)) •
            (Work.MotV.kleinCoord D L i * Work.MotV.kleinCoord D L j) from by
      rw [Algebra.smul_def, map_mul]; ring]
    exact Submodule.smul_mem _ _ (pair_mem_range D L i j)
  exact key x y

/-- `kPhi` applied to the coefficient vector of `p_k` is `p_k (κ)`. -/
lemma kPhi_lamVec (aL bL : L) (haL : aL = algebraMap 𝕜 L D.a)
    (hbL : bL = algebraMap 𝕜 L D.b) (k : Fin 5) :
    kPhi D L (lamVec aL bL k) =
      Work.MotK.kleinP (algebraMap 𝕜 FF D.a) (algebraMap 𝕜 FF D.b)
        (Work.MotV.kleinCoord D L) k := by
  fin_cases k <;>
    simp only [lamVec, lamIdx, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.cons_val] <;>
    simp only [map_add, map_smul, kPhi_single] <;>
    simp only [idxPair, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.cons_val] <;>
    simp only [Algebra.smul_def, haL, hbL, IsScalarTower.algebraMap_apply 𝕜 L FF] <;>
    simp only [Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
      Work.MotK.kleinP3, Work.MotK.kleinP4, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val] <;>
    push_cast <;> ring

lemma lamVec_mem_ker (aL bL : L) (haL : aL = algebraMap 𝕜 L D.a)
    (hbL : bL = algebraMap 𝕜 L D.b)
    (hklein : ∀ k : Fin 5, Work.MotK.kleinP (algebraMap 𝕜 FF D.a) (algebraMap 𝕜 FF D.b)
      (Work.MotV.kleinCoord D L) k = 0) (k : Fin 5) :
    kPhi D L (lamVec aL bL k) = 0 := by
  rw [kPhi_lamVec D L aL bL haL hbL k, hklein k]

/-- `kPhi` applied to `cVec` is `2a κ₀² − b κ₁κ₄`. -/
lemma kPhi_cVec (aL bL : L) (haL : aL = algebraMap 𝕜 L D.a) (hbL : bL = algebraMap 𝕜 L D.b) :
    kPhi D L (cVec aL bL) =
      2 * algebraMap 𝕜 FF D.a * (Work.MotV.kleinCoord D L 0) ^ 2
        - algebraMap 𝕜 FF D.b * Work.MotV.kleinCoord D L 1 * Work.MotV.kleinCoord D L 4 := by
  show kPhi D L ((aL + aL) • Pi.single (0 : Fin 15) (1 : L)
    + (-bL) • Pi.single (8 : Fin 15) (1 : L)) = _
  simp only [map_add, map_smul, kPhi_single, idxPair, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val]
  simp only [Algebra.smul_def, haL, hbL, IsScalarTower.algebraMap_apply 𝕜 L FF]
  push_cast
  first | refl_ring1 | ring

/-! ## §3 The main computation -/

/-- **The key non-degeneracy**: for a Klein datum and a `spans` witness `e`, the quadratic form
`2 a κ₀² − b κ₁κ₄` does not vanish in `L(E)`. -/
theorem kleinQuad_ne_zero (aL bL : L) (haL : aL = algebraMap 𝕜 L D.a)
    (hbL : bL = algebraMap 𝕜 L D.b) (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m : Fin 5, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L FF (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (hklein : ∀ k : Fin 5, Work.MotK.kleinP (algebraMap 𝕜 FF D.a) (algebraMap 𝕜 FF D.b)
      (Work.MotV.kleinCoord D L) k = 0)
    (hab : aL * bL ≠ 0) :
    2 * algebraMap 𝕜 FF D.a * (Work.MotV.kleinCoord D L 0) ^ 2
      - algebraMap 𝕜 FF D.b * Work.MotV.kleinCoord D L 1 * Work.MotV.kleinCoord D L 4 ≠ 0 := by
  classical
  have ha : aL ≠ 0 := fun h => hab (by rw [h, zero_mul])
  have hb : bL ≠ 0 := fun h => hab (by rw [h, mul_zero])
  have hfr : FiniteDimensional L ↥(kPhi D L).range :=
    FiniteDimensional.of_surjective (LinearMap.rangeRestrict (kPhi D L))
      (LinearMap.surjective_rangeRestrict _)
  haveI := hfr
  -- the ten monomials lie in the range, which therefore has dimension `≥ 10`
  have hspan_le : Submodule.span L (Set.range (Work.MotTDG.tenMon (D.E.baseChange L)))
      ≤ (kPhi D L).range := by
    rw [Submodule.span_le]
    rintro x ⟨t, rfl⟩
    exact tenMon_mem_range D L e he t
  have hfin10 : Module.finrank L ↥(Submodule.span L
      (Set.range (Work.MotTDG.tenMon (D.E.baseChange L)))) = 10 := by
    rw [finrank_span_eq_card (Work.MotTDG.tenMon_linearIndependent (D.E.baseChange L))]
    simp
  -- the five Pfaffian relations lie in the kernel, which therefore has dimension `≥ 5`
  have hlam_le : Submodule.span L (Set.range (lamVec aL bL))
      ≤ LinearMap.ker (kPhi D L) := by
    rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    exact lamVec_mem_ker D L aL bL haL hbL hklein k
  have hfin_lam : Module.finrank L ↥(Submodule.span L (Set.range (lamVec aL bL))) = 5 := by
    rw [finrank_span_eq_card (lamVec_linearIndependent aL bL hab)]
    simp
  -- rank--nullity
  have hrn : Module.finrank L ↥(kPhi D L).range
      + Module.finrank L ↥(LinearMap.ker (kPhi D L)) = 15 := by
    have h := LinearMap.finrank_range_add_finrank_ker (kPhi D L)
    rwa [Module.finrank_fin_fun] at h
  have hker5 : 5 ≤ Module.finrank L ↥(LinearMap.ker (kPhi D L)) := by
    have h := Submodule.finrank_mono hlam_le
    rwa [hfin_lam] at h
  have hQ10 : Module.finrank L ↥(kPhi D L).range = 10 := by
    have h := Submodule.finrank_mono hspan_le
    rw [hfin10] at h
    omega
  have hker5' : Module.finrank L ↥(LinearMap.ker (kPhi D L)) = 5 := by omega
  have hker_eq : LinearMap.ker (kPhi D L) = Submodule.span L (Set.range (lamVec aL bL)) :=
    (Submodule.eq_of_le_of_finrank_le hlam_le (by rw [hker5', hfin_lam])).symm
  -- `cVec` is not a relation
  have hcQ : cVec aL bL ∉ Submodule.span L (Set.range (lamVec aL bL)) := by
    intro hmem
    have hzero : psi aL bL (cVec aL bL) = 0 := by
      refine Submodule.span_induction (p := fun v _ => psi aL bL v = 0) ?_ ?_ ?_ ?_ hmem
      · rintro x ⟨k, rfl⟩; exact psi_lamVec aL bL hb k
      · simp
      · intro x y hx hy hpx hpy; rw [map_add, hpx, hpy, add_zero]
      · intro c x hx hpx; rw [map_smul, hpx, smul_zero]
    rw [psi_cVec aL bL hb] at hzero
    exact (div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 ha)) hb) hzero
  have hne : kPhi D L (cVec aL bL) ≠ 0 := by
    intro h0
    exact hcQ (by rw [← hker_eq]; exact h0)
  rw [kPhi_cVec D L aL bL haL hbL] at hne
  exact hne

end Main

/-! ## §4 The target statement -/

theorem KleinNondeg (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) :
    2 * algebraMap K (Work.MotK.OmG K D) D.a * (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) ^ 2
      - algebraMap K (Work.MotK.OmG K D) D.b * Work.MotV.kleinCoord D (Work.MotK.KbG K) 1
        * Work.MotV.kleinCoord D (Work.MotK.KbG K) 4 ≠ 0 := by
  obtain ⟨e, he⟩ := hD.spans
  have hab : algebraMap K (Work.MotK.KbG K) D.a * algebraMap K (Work.MotK.KbG K) D.b ≠ 0 := by
    rw [← map_mul]
    intro h0
    have h1 : algebraMap K (Work.MotK.KbG K) ((D.a * D.b)⁻¹)
        * algebraMap K (Work.MotK.KbG K) (D.a * D.b) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hD.ab_ne, map_one]
    rw [h0, mul_zero] at h1
    exact one_ne_zero h1.symm
  have h := kleinQuad_ne_zero D (Work.MotK.KbG K)
    (algebraMap K (Work.MotK.KbG K) D.a) (algebraMap K (Work.MotK.KbG K) D.b)
    rfl rfl e (he (Work.MotK.KbG K)) (fun k => hD.klein_eq (Work.MotK.KbG K) k) hab
  simpa only [IsScalarTower.algebraMap_apply K (Work.MotK.KbG K) (Work.MotK.OmG K D)] using h

end Work.MotK.TwRuling
