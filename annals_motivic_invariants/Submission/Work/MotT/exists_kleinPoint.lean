import Mathlib
import Submission.Work.MotT.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.MotC2.InfPlaceCore
import Submission.Work.MotC2.PoleOrder
import Submission.Work.MotC2.Relations
import Submission.Work.MotT.kPointAux
import Submission.Work.MotT.infW_genX_sub_one_mem
import Submission.Work.MotT.exists_norm_basis
import Submission.Work.MotT.kleinP_of_mem_maximalIdeal
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

/-! ## §1 The Klein quadrics are polynomials

Two elementary facts about the five Pfaffian quadrics `p_0, …, p_4 = kleinP a b ·`: they are
compatible with every ring homomorphism (they have integer coefficients) and they are homogeneous of
degree two. -/

/-- The Klein quadrics commute with ring homomorphisms. -/
theorem kleinP_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R)
    (x : Fin 5 → R) (k : Fin 5) :
    f (Work.MotK.kleinP a b x k) = Work.MotK.kleinP (f a) (f b) (fun i => f (x i)) k := by
  fin_cases k <;>
    simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
      Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1,
      Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4, map_add, map_sub, map_mul, map_pow,
      map_neg]

/-- The Klein quadrics are homogeneous of degree two. -/
theorem kleinP_scale {R : Type*} [CommRing R] (a b t : R) (x : Fin 5 → R) (k : Fin 5) :
    Work.MotK.kleinP a b (fun i => t * x i) k = t ^ 2 * Work.MotK.kleinP a b x k := by
  fin_cases k <;>
    simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
      Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1,
      Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4] <;> ring

/-! ## §2 The largest non-zero column of the coordinate matrix -/

/-- The largest column index `m₀` carrying a nonzero entry of the coordinate matrix `D.coord`. -/
theorem exists_max_coord_index {K : Type} [Field K] (D : Work.MotV.KleinData K)
    (h : ∃ m : Fin 5, ∃ i : Fin 5, D.coord i m ≠ 0) :
    ∃ m₀ : Fin 5, (∃ i : Fin 5, D.coord i m₀ ≠ 0) ∧
      ∀ m : Fin 5, m₀ < m → ∀ i : Fin 5, D.coord i m = 0 := by
  classical
  obtain ⟨m₀, i₀, hi₀⟩ := h
  have hne : (Finset.univ.filter (fun m : Fin 5 => ∃ i : Fin 5, D.coord i m ≠ 0)).Nonempty :=
    ⟨m₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i₀, hi₀⟩⟩
  refine ⟨(Finset.univ.filter (fun m : Fin 5 => ∃ i : Fin 5, D.coord i m ≠ 0)).max' hne, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  · intro m hlt i
    by_contra hc
    have hle : m ≤ (Finset.univ.filter (fun m : Fin 5 => ∃ i : Fin 5, D.coord i m ≠ 0)).max' hne :=
      Finset.le_max' _ m (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hc⟩)
    exact absurd hle (not_le.mpr hlt)

/-! ## §3 Evaluation of the Klein coordinates at the point at infinity

Let `m₀` be the largest index with a nonzero column of `D.coord` and let `e = kP m₀`.  The Klein
coordinate `κ_i = kleinCoord D K i` satisfies `w ^ e · κ_i ∈ ↥(infPlace E)` and is congruent to the
constant `D.coord i m₀` modulo the maximal ideal of the local ring at infinity, where
`w = infW E = y/x²` is the uniformizer.  The proof is the `O`-adic computation described in the
docstring of `exists_kleinPoint`: `w^{kP m}·b_m = g^{kQ m}` with `g = w²x ≡ 1 mod 𝔪` for the five
basis elements `b_m`, so `w^e κ_i = Σ_{m ≤ m₀} D.coord i m · w^{e-kP m}·g^{kQ m}`, whose terms below
`m₀` are divisible by `w` and whose `m₀`-term is `D.coord i m₀·g^{kQ m₀} ≡ D.coord i m₀`. -/
lemma exists_eval_at_O {K : Type} [Field K] (D : Work.MotV.KleinData K) (m₀ : Fin 5)
    (hm₀ : ∀ m : Fin 5, m₀ < m → ∀ i : Fin 5, D.coord i m = 0)
    (hg : ((⟨Work.MotC2.genX (D.E.baseChange K) * (Work.MotC2.infW (D.E.baseChange K)) ^ 2,
        Work.MotC2.genX_mul_infW_sq_mem_infPlace (D.E.baseChange K)⟩ :
          ↥(Work.MotC2.infPlace (D.E.baseChange K))) - 1) ∈
      IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace (D.E.baseChange K)))
    (N : Fin 5 → ↥(Work.MotC2.infPlace (D.E.baseChange K)))
    (hNval : ∀ m : Fin 5, (N m : Work.MotC2.Func (D.E.baseChange K)) =
        (Work.MotC2.infW (D.E.baseChange K)) ^ (kP m) * Work.MotV.kleinBas D K m)
    (hN1 : ∀ m : Fin 5, N m - 1 ∈ IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace (D.E.baseChange K)))
    (i : Fin 5) :
    ∃ X : ↥(Work.MotC2.infPlace (D.E.baseChange K)),
      (X : Work.MotC2.Func (D.E.baseChange K)) =
          (Work.MotC2.infW (D.E.baseChange K)) ^ (kP m₀) * Work.MotV.kleinCoord D K i ∧
      X - algebraMap K ↥(Work.MotC2.infPlace (D.E.baseChange K)) (D.coord i m₀) ∈
        IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace (D.E.baseChange K)) := by
  classical
  -- the uniformizer `w = y/x²`, which lies in the maximal ideal
  have hw_mem : (⟨Work.MotC2.infW (D.E.baseChange K),
        Work.MotC2.InfPlaceCore.infW_mem_infPlace (D.E.baseChange K)⟩ :
        ↥(Work.MotC2.infPlace (D.E.baseChange K))) ∈
      IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace (D.E.baseChange K)) := by
    have heq : (⟨Work.MotC2.infW (D.E.baseChange K),
          Work.MotC2.InfPlaceCore.infW_mem_infPlace (D.E.baseChange K)⟩ :
          ↥(Work.MotC2.infPlace (D.E.baseChange K))) =
        algebraMap (Work.MotC2.infCoordRing (D.E.baseChange K))
          ↥(Work.MotC2.infPlace (D.E.baseChange K)) (Work.MotC2.InfPlaceCore.W (D.E.baseChange K)) := by
      apply Subtype.ext
      show Work.MotC2.infW (D.E.baseChange K) =
        (Work.MotC2.InfPlaceCore.W (D.E.baseChange K) : Work.MotC2.Func (D.E.baseChange K))
      rw [Work.MotC2.InfPlaceCore.coe_W]
    rw [heq, Work.MotC2.InfPlaceCore.maxIdeal_eq_span]
    exact Ideal.subset_span (Set.mem_singleton _)
  let w : ↥(Work.MotC2.infPlace (D.E.baseChange K)) :=
    ⟨Work.MotC2.infW (D.E.baseChange K), Work.MotC2.InfPlaceCore.infW_mem_infPlace (D.E.baseChange K)⟩
  have hwmem : w ∈ IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace (D.E.baseChange K)) := hw_mem
  -- the normalised basis elements
  let T : Fin 5 → ↥(Work.MotC2.infPlace (D.E.baseChange K)) := fun m =>
    if kP m ≤ kP m₀ then w ^ (kP m₀ - kP m) * N m else 0
  have hTpos : ∀ m (h : kP m ≤ kP m₀),
      (T m : Work.MotC2.Func (D.E.baseChange K)) =
        (Work.MotC2.infW (D.E.baseChange K)) ^ (kP m₀ - kP m) *
          (N m : Work.MotC2.Func (D.E.baseChange K)) := by
    intro m h
    simp only [T, if_pos h, Subalgebra.coe_mul, Subalgebra.coe_pow, w]
  have hTneg : ∀ m (h : ¬ kP m ≤ kP m₀),
      (T m : Work.MotC2.Func (D.E.baseChange K)) = 0 := by
    intro m h
    simp only [T, if_neg h, Subalgebra.coe_zero]
  -- the element of the local ring at infinity
  let X : ↥(Work.MotC2.infPlace (D.E.baseChange K)) :=
    ∑ m : Fin 5, algebraMap K ↥(Work.MotC2.infPlace (D.E.baseChange K)) (D.coord i m) * T m
  have hXval : (X : Work.MotC2.Func (D.E.baseChange K)) =
      (Work.MotC2.infW (D.E.baseChange K)) ^ (kP m₀) * Work.MotV.kleinCoord D K i := by
    have h1 : (X : Work.MotC2.Func (D.E.baseChange K)) =
        ∑ m : Fin 5, algebraMap K (Work.MotC2.Func (D.E.baseChange K)) (D.coord i m) *
          (T m : Work.MotC2.Func (D.E.baseChange K)) := by
      simp only [X]
      push_cast
      rfl
    refine h1.trans ?_
    have h2 : (∑ m : Fin 5, algebraMap K (Work.MotC2.Func (D.E.baseChange K)) (D.coord i m) *
          (T m : Work.MotC2.Func (D.E.baseChange K))) =
        ∑ m : Fin 5, algebraMap K (Work.MotC2.Func (D.E.baseChange K)) (D.coord i m) *
          ((Work.MotC2.infW (D.E.baseChange K)) ^ (kP m₀) * Work.MotV.kleinBas D K m) := by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      by_cases h : kP m ≤ kP m₀
      · rw [hTpos m h, hNval m]
        congr 1
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h]
      · rw [hTneg m h]
        have hm : m₀ < m := by
          by_contra hle
          exact h (kP_le_iff.mpr (not_lt.mp hle))
        simp only [hm₀ m hm i, map_zero, zero_mul, mul_zero]
    refine h2.trans ?_
    have h3 : (∑ m : Fin 5, algebraMap K (Work.MotC2.Func (D.E.baseChange K)) (D.coord i m) *
          ((Work.MotC2.infW (D.E.baseChange K)) ^ (kP m₀) * Work.MotV.kleinBas D K m)) =
        (Work.MotC2.infW (D.E.baseChange K)) ^ (kP m₀) *
          ∑ m : Fin 5, algebraMap K (Work.MotC2.Func (D.E.baseChange K)) (D.coord i m) *
            Work.MotV.kleinBas D K m := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    refine h3.trans ?_
    have h4 : (∑ m : Fin 5, algebraMap K (Work.MotC2.Func (D.E.baseChange K)) (D.coord i m) *
          Work.MotV.kleinBas D K m) = Work.MotV.kleinCoord D K i := by
      rw [Work.MotV.kleinCoord_eq_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      simp
    rw [h4]
  -- the leading term
  have hm₀A : m₀ ∈ Finset.univ.filter (fun m : Fin 5 => kP m ≤ kP m₀) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
  have hXsum : X = ∑ m ∈ Finset.univ.filter (fun m : Fin 5 => kP m ≤ kP m₀),
      algebraMap K ↥(Work.MotC2.infPlace (D.E.baseChange K)) (D.coord i m) *
        (w ^ (kP m₀ - kP m) * N m) := by
    have h1 : X = ∑ m : Fin 5, (if kP m ≤ kP m₀ then
        algebraMap K ↥(Work.MotC2.infPlace (D.E.baseChange K)) (D.coord i m) *
          (w ^ (kP m₀ - kP m) * N m) else 0) := by
      simp only [X]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      by_cases h : kP m ≤ kP m₀ <;> simp [T, h]
    rw [h1, ← Finset.sum_filter]
  have hdecomp : X - algebraMap K ↥(Work.MotC2.infPlace (D.E.baseChange K)) (D.coord i m₀) =
      algebraMap K ↥(Work.MotC2.infPlace (D.E.baseChange K)) (D.coord i m₀) * (N m₀ - 1) +
        ∑ m ∈ (Finset.univ.filter (fun m : Fin 5 => kP m ≤ kP m₀)).erase m₀,
          algebraMap K ↥(Work.MotC2.infPlace (D.E.baseChange K)) (D.coord i m) *
            (w ^ (kP m₀ - kP m) * N m) := by
    rw [hXsum, ← Finset.add_sum_erase _ _ hm₀A, Nat.sub_self, pow_zero, one_mul]
    first | refl_ring1 | ring
  have hXmem : X - algebraMap K ↥(Work.MotC2.infPlace (D.E.baseChange K)) (D.coord i m₀) ∈
      IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace (D.E.baseChange K)) := by
    rw [hdecomp]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hN1 m₀)) (Ideal.sum_mem _ (fun m hm => ?_))
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hm
    have hle : m ≤ m₀ := kP_le_iff.mp (Finset.mem_filter.mp hmem).2
    have hlt : m < m₀ := lt_of_le_of_ne hle hne
    have hpos : 1 ≤ kP m₀ - kP m := by
      have := kP_lt_iff.mpr hlt
      omega
    have hterm : algebraMap K ↥(Work.MotC2.infPlace (D.E.baseChange K)) (D.coord i m) *
          (w ^ (kP m₀ - kP m) * N m) =
        (algebraMap K ↥(Work.MotC2.infPlace (D.E.baseChange K)) (D.coord i m) *
          (w ^ (kP m₀ - kP m - 1) * N m)) * w := by
      set n : ℕ := kP m₀ - kP m - 1 with hn
      have hx : kP m₀ - kP m = n + 1 := by omega
      rw [hx, pow_succ]
      first | refl_ring1 | ring
    rw [hterm]
    exact Ideal.mul_mem_left _ _ hwmem
  exact ⟨X, hXval, hXmem⟩

/-! ## §4 The main theorem -/

/-- The main assembly: given the `O`-adic input `hg` (`w²x ≡ 1 mod 𝔪`), the normalised basis `N`
(`w^{kP m}·b_m = N m ≡ 1 mod 𝔪`) and the reduction step `hred` at a rational place, the Klein curve
has a `K`-point `y i = D.coord i m₀`. -/
private lemma exists_kleinPoint_of_inputs {K : Type} [Field K] (D : Work.MotV.KleinData K)
    (hD : D.Good)
    (hg : ((⟨Work.MotC2.genX (D.E.baseChange K) * (Work.MotC2.infW (D.E.baseChange K)) ^ 2,
        Work.MotC2.genX_mul_infW_sq_mem_infPlace (D.E.baseChange K)⟩ :
          ↥(Work.MotC2.infPlace (D.E.baseChange K))) - 1) ∈
      IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace (D.E.baseChange K)))
    (N : Fin 5 → ↥(Work.MotC2.infPlace (D.E.baseChange K)))
    (hNval : ∀ m : Fin 5, (N m : Work.MotC2.Func (D.E.baseChange K)) =
        (Work.MotC2.infW (D.E.baseChange K)) ^ (kP m) * Work.MotV.kleinBas D K m)
    (hN1 : ∀ m : Fin 5, N m - 1 ∈ IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace (D.E.baseChange K)))
    (hred : ∀ (E : WeierstrassCurve K) (a b : K) (y : Fin 5 → K)
      (X : Fin 5 → ↥(Work.MotC2.infPlace E)),
      (∀ i, X i - algebraMap K ↥(Work.MotC2.infPlace E) (y i) ∈
        IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace E)) →
      (∀ k, Work.MotK.kleinP (algebraMap K (Work.MotC2.Func E) a)
        (algebraMap K (Work.MotC2.Func E) b) (fun i => (X i : Work.MotC2.Func E)) k = 0) →
      ∀ k, Work.MotK.kleinP a b y k = 0) :
    ∃ y : Fin 5 → K, y ≠ 0 ∧ ∀ k, Work.MotK.kleinP D.a D.b y k = 0 := by
  classical
  have hex : ∃ m : Fin 5, ∃ i : Fin 5, D.coord i m ≠ 0 := by
    by_contra h
    push_neg at h
    refine hD.coord0_ne K ?_
    simp only [Work.MotV.kleinCoord]
    refine Finset.sum_eq_zero fun m _ => ?_
    simp only [h m 0, map_zero, zero_mul]
  obtain ⟨m₀, ⟨i₀, hi₀⟩, hm₀⟩ := exists_max_coord_index D hex
  -- choose the witnesses `X i` of the `O`-adic evaluation
  choose X hXval hXmem using fun i => exists_eval_at_O D m₀ hm₀ hg N hNval hN1 i
  refine ⟨fun i => D.coord i m₀, ?_, ?_⟩
  · intro hzero
    exact hi₀ (by have := congrFun hzero i₀; simpa using this)
  · refine hred (D.E.baseChange K) D.a D.b (fun i => D.coord i m₀) X hXmem ?_
    intro k
    have h1 : (fun i => (X i : Work.MotC2.Func (D.E.baseChange K))) =
        fun i => (Work.MotC2.infW (D.E.baseChange K)) ^ (kP m₀) * Work.MotV.kleinCoord D K i :=
      funext hXval
    rw [h1, kleinP_scale, hD.klein_eq K k, mul_zero]

/-- **The Klein curve has a `K`-point in coordinates.** For `D.Good` there is a nonzero
`y : Fin 5 → K` satisfying the five Klein quadrics `kleinP D.a D.b y k = 0`.  Equivalently, the
Klein model `C = V(p_0,…,p_4) ⊂ ℙ⁴` of `D.E` has a rational point.

This is needed by `Work.MotT.twist_iso_pointK`: the isomorphism hypothesis forces
`h₁ ≡ ± h₂` modulo fifth powers (`C_{h₁} ≅ C_{h₂}`), and then the conclusion
`kleinTw a b g y = 0` with `g = μ^5` reduces (via `Work.MotV.kleinTw_subst`) to a `K`-point of the
Klein curve `kleinP a b`.

Witness and route (agreed in review): let `m₀` be the largest `m` such that the column
`D.coord · m` is nonzero (exists by `hD.coord0_ne`, e.g. at `L = K`); then `y := fun i => D.coord i m₀`
works.  Put `t = genX/genY` (order `1` at `O`), so `t ^ (2 * m₀) * κ_i` is regular at `O` with value
`D.coord i m₀ * λ` for a fixed `λ ≠ 0`; multiplying the identity `kleinP a b (kleinCoord D K̄ ·) = 0`
(`hD.klein_eq` at `L = KbK K`) by `(t ^ m₀)^2` and evaluating at `O` (a ring homomorphism on the
local ring at `O`, available in `Work.MotC2`: `infCoordRing`, `infPlace`, `PoleOrder`) gives
`kleinP a b y = 0`. -/
theorem exists_kleinPoint {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) :
    ∃ y : Fin 5 → K, y ≠ 0 ∧ ∀ k, Work.MotK.kleinP D.a D.b y k = 0 := by
  have hg := infW_genX_sub_one_mem (D.E.baseChange K)
  obtain ⟨N, hNval, hN1⟩ := exists_norm_basis D hg
  exact exists_kleinPoint_of_inputs D hD hg N hNval hN1
    (fun E a b y X hX h0 => kleinP_of_mem_maximalIdeal E a b y X hX h0)

end

end Work.MotT
