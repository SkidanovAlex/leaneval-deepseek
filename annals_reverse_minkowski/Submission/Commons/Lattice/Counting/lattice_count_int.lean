import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Lattice.SuccessiveMinima.realisation_linearIndependent
import Submission.Commons.Lattice.SuccessiveMinima.exact_realization
import Submission.Commons.Lattice.SuccessiveMinima.positive
import Submission.Commons.Lattice.SuccessiveMinima.interior_exclusion
import Submission.Commons.Lattice.Minkowski.flag_basis
import Submission.Commons.Lattice.Counting.divisibility_tower

namespace Commons.Lattice.Counting

open Set Filter Metric BigOperators
open _root_.Module _root_.Submodule
open scoped BigOperators
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

/-!
# Counting lattice points in a ball via successive minima
-/

namespace latticeCountIntHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Iterated divisibility along a chain `n (k+1) ∣ n k`: `n (a+m) ∣ n a`. -/
lemma dvd_iter_chain {d : ℕ} {n : ℕ → ℕ}
    (hstep : ∀ k : ℕ, 1 ≤ k → k < d → n (k + 1) ∣ n k) :
    ∀ {a m : ℕ}, 1 ≤ a → a + m ≤ d → n (a + m) ∣ n a := by
  intro a m ha1
  induction m with
  | zero =>
      intro h
      rfl
  | succ m ih =>
      intro h
      have hle : a + m ≤ d := by omega
      have hlt : a + m < d := by omega
      have hk1 : 1 ≤ a + m := by omega
      have hb : n (a + m + 1) ∣ n (a + m) := hstep (a + m) hk1 hlt
      exact dvd_trans hb (ih hle)

/-- If `n (k+1) ∣ n k` for `1 ≤ k < d`, then `n b ∣ n a` whenever `1 ≤ a ≤ b ≤ d`. -/
lemma dvd_chain {d : ℕ} {n : ℕ → ℕ}
    (hstep : ∀ k : ℕ, 1 ≤ k → k < d → n (k + 1) ∣ n k) {a b : ℕ}
    (ha1 : 1 ≤ a) (hab : a ≤ b) (hbd : b ≤ d) : n b ∣ n a := by
  have h := dvd_iter_chain (d := d) (n := n) hstep (a := a) ha1 (m := b - a) (by omega)
  simpa [Nat.add_sub_of_le hab] using h

/-- The span of the first `m` vectors (as a `Fin m` family) equals the span of the
`Fin d`-family restricted to indices `< m`. -/
lemma span_prefix_eq_lt {d m : ℕ} (hm : m ≤ d) (w : Fin d → E) :
    Submodule.span ℝ (Set.range (fun j : Fin m => w ⟨j.val, by omega⟩)) =
    Submodule.span ℝ {x : E | ∃ j : Fin d, j.val < m ∧ x = w j} := by
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨⟨j.val, by omega⟩, j.isLt, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j.val, hj⟩, rfl⟩

/-- If `z` lies in the span of the first `k.val` vectors of a real basis `b` of `E`,
then the `k`-th coordinate of `z` (in that basis) vanishes. -/
lemma coord_zero_of_mem_span_lt {d : ℕ} (b : Module.Basis (Fin d) ℝ E) (k : Fin d) {z : E}
    (hz : z ∈ Submodule.span ℝ {x : E | ∃ j : Fin d, j.val < k.val ∧ x = (b j : E)}) :
    b.coord k z = 0 := by
  classical
  rw [← span_prefix_eq_lt (d := d) (m := k.val) (w := fun j : Fin d => (b j : E)) (le_of_lt k.isLt)] at hz
  rw [Submodule.mem_span_range_iff_exists_fun] at hz
  rcases hz with ⟨c, hc⟩
  rw [← hc]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hne : (⟨j.val, by omega⟩ : Fin d) ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  simp [Module.Basis.coord_apply, Module.Basis.repr_self, hne]

/-- Applying the `k`-th coordinate functional of a basis to the coordinate expansion
extracts the `k`-th coefficient. -/
lemma coord_apply_sum {d : ℕ} (b : Module.Basis (Fin d) ℝ E) (k : Fin d) (c : Fin d → ℝ) :
    b.coord k (∑ j, c j • b j) = c k := by
  classical
  rw [map_sum]
  rw [Finset.sum_eq_single k]
  · simp [Module.Basis.coord_apply]
  · intro j hj hjk
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, hjk]
  · intro hk
    exact False.elim (hk (Finset.mem_univ k))

/-- Product bound from a divisibility tower: if `n d = q d` and `n k < 2 * q k` for every
`1 ≤ k ≤ d`, then `∏_{i : Fin d} n (i.val + 1) ≤ 2^(d-1) * ∏_{i : Fin d} q (i.val + 1)`. -/
lemma prod_tower_le_prod_q {d : ℕ} (hd1 : 1 ≤ d) (q n : ℕ → ℕ)
    (hn_top : n d = q d) (hn_lt : ∀ k : ℕ, 1 ≤ k → k ≤ d → n k < 2 * q k) :
    (∏ i : Fin d, n (i.val + 1)) ≤ 2 ^ (d - 1) * ∏ i : Fin d, q (i.val + 1) := by
  classical
  let d1 : ℕ := d - 1
  have hd_eq : d = d1 + 1 := by
    dsimp [d1]
    omega
  -- ∏ over Fin d splits into prefix (Fin d1) times last
  have hsplit_n : (∏ i : Fin d, n (i.val + 1)) =
      (∏ i : Fin d1, n (i.val + 1)) * n d := by
    rw [hd_eq]
    symm
    have h := Fin.prod_univ_castSucc (n := d1) (f := fun i : Fin (d1 + 1) => n (i.val + 1))
    simpa [hd_eq] using h.symm
  have hsplit_q : (∏ i : Fin d, q (i.val + 1)) =
      (∏ i : Fin d1, q (i.val + 1)) * q d := by
    rw [hd_eq]
    symm
    have h := Fin.prod_univ_castSucc (n := d1) (f := fun i : Fin (d1 + 1) => q (i.val + 1))
    simpa [hd_eq] using h.symm
  have hpref : (∏ i : Fin d1, n (i.val + 1)) ≤ ∏ i : Fin d1, (2 * q (i.val + 1)) := by
    apply Finset.prod_le_prod
    · intro i hi
      exact Nat.zero_le _
    · intro i hi
      have hk1 : 1 ≤ i.val + 1 := by omega
      have hk_le : i.val + 1 ≤ d := by
        have hi' : i.val < d1 := i.isLt
        dsimp [d1] at hi'
        omega
      exact Nat.le_of_lt (hn_lt (i.val + 1) hk1 hk_le)
  have hpref_pow : (∏ i : Fin d1, (2 * q (i.val + 1))) =
      2 ^ d1 * ∏ i : Fin d1, q (i.val + 1) := by
    calc
      (∏ i : Fin d1, (2 * q (i.val + 1))) = (∏ i : Fin d1, 2) * ∏ i : Fin d1, q (i.val + 1) := by
        rw [Finset.prod_mul_distrib]
      _ = 2 ^ d1 * ∏ i : Fin d1, q (i.val + 1) := by
        simp
  calc
    (∏ i : Fin d, n (i.val + 1)) = (∏ i : Fin d1, n (i.val + 1)) * n d := hsplit_n
    _ ≤ (∏ i : Fin d1, (2 * q (i.val + 1))) * n d := by
      exact Nat.mul_le_mul_right _ hpref
    _ = (2 ^ d1 * ∏ i : Fin d1, q (i.val + 1)) * n d := by rw [hpref_pow]
    _ = 2 ^ d1 * ((∏ i : Fin d1, q (i.val + 1)) * n d) := by ring
    _ ≤ 2 ^ d1 * ((∏ i : Fin d1, q (i.val + 1)) * q d) := by
      have hnd : n d ≤ q d := by rw [hn_top]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hnd)
    _ = 2 ^ (d - 1) * ∏ i : Fin d, q (i.val + 1) := by
      have hpow : 2 ^ d1 = 2 ^ (d - 1) := by
        simp [d1]
      rw [hsplit_q, ← hpow]

end latticeCountIntHelpers

open latticeCountIntHelpers


/-- Counting step: the number of lattice points in the ball of radius `N` is bounded by the
product of a divisibility tower `n` with `q k ≤ n k` (and `q k > 2N/λₖ`). -/
theorem lattice_count_int_tower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {d : ℕ} (hfin : Module.finrank ℤ L = d) (hd1 : 1 ≤ d) (N : ℕ) (hN : 1 ≤ N)
    (q : ℕ → ℕ)
    (hq1 : ∀ k : ℕ, 1 ≤ k → k ≤ d → 1 ≤ q k)
    (hq_mono : ∀ k : ℕ, 1 ≤ k → k < d → q (k + 1) ≤ q k)
    (hq_gt : ∀ k : ℕ, 1 ≤ k → k ≤ d →
      (2 * (N : ℝ)) / Commons.Lattice.SuccessiveMinima.successiveMinimum L k < (q k : ℝ))
    (n : ℕ → ℕ) (hn_top : n d = q d)
    (hn_bound : ∀ k : ℕ, 1 ≤ k → k ≤ d → q k ≤ n k ∧ n k < 2 * q k)
    (hn_dvd : ∀ k : ℕ, 1 ≤ k → k < d → n (k + 1) ∣ n k) :
    (Nat.card {v : L // ‖(v : E)‖ ≤ N} : ℕ) ≤ ∏ i : Fin d, n (i.val + 1) := by
  classical
  haveI : Fintype {v : L // ‖(v : E)‖ ≤ N} := by
    exact Set.Finite.fintype
      (Commons.Lattice.SuccessiveMinima.finite_lattice_in_ball L (N : ℝ))
  -- positivity of the successive minima on 1..d
  have hmu_pos : ∀ k : ℕ, 1 ≤ k → k ≤ d →
      0 < Commons.Lattice.SuccessiveMinima.successiveMinimum L k := by
    intro k hk1 hkd
    exact Commons.Lattice.SuccessiveMinima.positive L k hk1 (by simpa [hfin] using hkd)
  -- n is positive where needed
  have hnpos : ∀ k : ℕ, 1 ≤ k → k ≤ d → 1 ≤ n k := by
    intro k hk1 hkd
    have hq1k := hq1 k hk1 hkd
    have hq_le := (hn_bound k hk1 hkd).1
    omega
  -- exact realisation of the successive minima, and a flag ℤ-basis of L
  rcases Commons.Lattice.SuccessiveMinima.exact_realization L d hfin with ⟨v, hvlin, hvbd⟩
  rcases Commons.Lattice.Minkowski.flag_basis L d hfin v hvlin with ⟨b, hbflag⟩
  let bR : Module.Basis (Fin d) ℝ E := b.ofZLatticeBasis ℝ L
  -- injectivity of the residue map
  have h_φ_inj :
      Function.Injective
        (fun x : {v : L // ‖(v : E)‖ ≤ N} => fun i : Fin d =>
          (b.repr x.1 i : ZMod (n (i.val + 1)))) := by
    intro x x' hxx'
    apply Subtype.ext
    by_contra hne
    let xL : L := x.1
    let xL' : L := x'.1
    let yL : L := xL - xL'
    have hy_ne : yL ≠ 0 := by
      dsimp [yL, xL, xL']
      exact sub_ne_zero.mpr hne
    let coef : Fin d → ℤ := fun i => b.repr xL i - b.repr xL' i
    -- expansion of y in the basis b
    have hy_exp : yL = ∑ i : Fin d, coef i • (b i : L) := by
      dsimp [yL, coef]
      calc
        xL - xL' = (∑ i : Fin d, b.repr xL i • (b i : L)) - (∑ i : Fin d, b.repr xL' i • (b i : L)) := by
          rw [Basis.sum_repr, Basis.sum_repr]
        _ = ∑ i : Fin d, (b.repr xL i - b.repr xL' i) • (b i : L) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [sub_smul]
    have hd_ne : coef ≠ 0 := by
      intro hc0
      apply hy_ne
      rw [hy_exp, hc0]
      simp
    -- divisibility of each coefficient, from the congruence of the residues
    have hdvd : ∀ i : Fin d, (n (i.val + 1) : ℤ) ∣ coef i := by
      intro i
      have hz : (b.repr xL i : ZMod (n (i.val + 1))) = (b.repr xL' i : ZMod (n (i.val + 1))) :=
        congrFun hxx' i
      have hz0 : ((b.repr xL i - b.repr xL' i : ℤ) : ZMod (n (i.val + 1))) = 0 := by
        rw [Int.cast_sub, hz]
        simp
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (b.repr xL i - b.repr xL' i) (n (i.val + 1))).mp hz0
    -- the top nonzero index
    let J : Finset (Fin d) := Finset.univ.filter (fun i : Fin d => coef i ≠ 0)
    have hJ : J.Nonempty := by
      by_contra hJ0
      apply hd_ne
      funext i
      by_contra hci
      have him : i ∈ J := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hci⟩
      exact hJ0 ⟨i, him⟩
    let k : Fin d := J.max' hJ
    have hdk : coef k ≠ 0 := by
      simpa [J] using (Finset.max'_mem J hJ)
    have htop : ∀ i : Fin d, k < i → coef i = 0 := by
      intro i hki
      by_contra hci
      have him : i ∈ J := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hci⟩
      have hle : i ≤ k := by
        simpa [k] using (Finset.le_max' J i him)
      exact (not_le_of_gt hki) hle
    -- divisibility by n (k.val + 1) for every coefficient
    have hdvd_k : ∀ i : Fin d, (n (k.val + 1) : ℤ) ∣ coef i := by
      intro i
      by_cases hik : i.val ≤ k.val
      · have hnat : n (k.val + 1) ∣ n (i.val + 1) := by
          apply dvd_chain (d := d) (n := n) hn_dvd (a := i.val + 1) (b := k.val + 1)
          · omega
          · omega
          · omega
        rcases hnat with ⟨t, ht⟩
        rcases hdvd i with ⟨s, hs⟩
        have htc : (n (i.val + 1) : ℤ) = (n (k.val + 1) : ℤ) * (t : ℤ) := by
          exact_mod_cast ht
        refine ⟨s * (t : ℤ), ?_⟩
        calc
          coef i = (n (i.val + 1) : ℤ) * s := hs
          _ = (n (k.val + 1) : ℤ) * (s * (t : ℤ)) := by
            rw [htc]
            ring
      · have hgt : k < i := lt_of_not_ge hik
        rw [htop i hgt]
        exact Int.dvd_zero _
    -- coefficients u of w; y = n (k.val+1) • w
    let u : Fin d → ℤ := fun i => Classical.choose (hdvd_k i)
    have hu : ∀ i : Fin d, coef i = (n (k.val + 1) : ℤ) * u i := by
      intro i
      exact Classical.choose_spec (hdvd_k i)
    have huk_ne : u k ≠ 0 := by
      have hdk' := hdk
      rw [hu k] at hdk'
      intro huk
      apply hdk'
      rw [huk]
      simp
    let w : L := ∑ i : Fin d, u i • (b i : L)
    have hw_coeffs : bR.coord k (w : E) = (u k : ℝ) := by
      have hwE : (w : E) = ∑ i : Fin d, ((u i : ℤ) : ℝ) • (bR i : E) := by
        simp [bR, w, ← Int.cast_smul_eq_zsmul ℝ]
      rw [hwE]
      -- apply the k-th coordinate: sum collapses to (u k : ℝ)
      have hsum := coord_apply_sum bR k (fun i : Fin d => ((u i : ℤ) : ℝ))
      simpa using hsum
    have hw_coord_ne : bR.coord k (w : E) ≠ 0 := by
      rw [hw_coeffs]
      exact_mod_cast huk_ne
    -- norm relations
    have hy_norm : ‖(yL : E)‖ ≤ 2 * (N : ℝ) := by
      have hx1 : ‖(xL : E)‖ ≤ (N : ℝ) := by simpa [xL] using x.2
      have hx2 : ‖(xL' : E)‖ ≤ (N : ℝ) := by simpa [xL'] using x'.2
      calc
        ‖(yL : E)‖ = ‖(xL : E) - (xL' : E)‖ := by simp [yL]
        _ ≤ ‖(xL : E)‖ + ‖(xL' : E)‖ := by
          simpa [sub_eq_add_neg, norm_neg] using (norm_add_le (xL : E) (-(xL' : E)))
        _ ≤ 2 * (N : ℝ) := by nlinarith
    have hmu_k_pos : 0 < Commons.Lattice.SuccessiveMinima.successiveMinimum L (k.val + 1) :=
      hmu_pos (k.val + 1) (by omega) (by omega)
    have hnk1 : 1 ≤ n (k.val + 1) := hnpos (k.val + 1) (by omega) (by omega)
    have hq_gt_k : (2 * (N : ℝ)) /
        Commons.Lattice.SuccessiveMinima.successiveMinimum L (k.val + 1) < (q (k.val + 1) : ℝ) :=
      hq_gt (k.val + 1) (by omega) (by omega)
    have hqk_le : q (k.val + 1) ≤ n (k.val + 1) := (hn_bound (k.val + 1) (by omega) (by omega)).1
    have h2lt : 2 * (N : ℝ) < (n (k.val + 1) : ℝ) *
        Commons.Lattice.SuccessiveMinima.successiveMinimum L (k.val + 1) := by
      have hmul : 2 * (N : ℝ) < (q (k.val + 1) : ℝ) *
          Commons.Lattice.SuccessiveMinima.successiveMinimum L (k.val + 1) := by
        have hqg := hq_gt_k
        rw [div_lt_iff₀ hmu_k_pos] at hqg
        simpa [mul_comm, mul_left_comm, mul_assoc] using hqg
      exact lt_of_lt_of_le hmul
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hqk_le) (le_of_lt hmu_k_pos))
    have hw_norm : ‖(w : E)‖ <
        Commons.Lattice.SuccessiveMinima.successiveMinimum L (k.val + 1) := by
      have hy_scaled : yL = (n (k.val + 1) : ℤ) • w := by
        rw [hy_exp]
        dsimp [w]
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [smul_smul, ← hu i]
      have hyz : (yL : E) = (n (k.val + 1) : ℝ) • (w : E) := by
        have hz1 : (yL : E) = (n (k.val + 1) : ℤ) • (w : E) := by
          simpa using congrArg (fun t : L => (t : E)) hy_scaled
        calc
          (yL : E) = (n (k.val + 1) : ℤ) • (w : E) := hz1
          _ = ((n (k.val + 1) : ℤ) : ℝ) • (w : E) := by
            rw [← Int.cast_smul_eq_zsmul ℝ (n (k.val + 1) : ℤ) (w : E)]
          _ = (n (k.val + 1) : ℝ) • (w : E) := by
            rw [show (((n (k.val + 1) : ℤ) : ℝ)) = (n (k.val + 1) : ℝ) by norm_num]

      have hyl_eq : ‖(yL : E)‖ = (n (k.val + 1) : ℝ) * ‖(w : E)‖ := by
        calc
          ‖(yL : E)‖ = ‖(n (k.val + 1) : ℝ) • (w : E)‖ := by rw [hyz]
          _ = (n (k.val + 1) : ℝ) * ‖(w : E)‖ := by
            have hnn : 0 ≤ (n (k.val + 1) : ℝ) := by positivity
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn]
      have hylt : ‖(yL : E)‖ < (n (k.val + 1) : ℝ) *
          Commons.Lattice.SuccessiveMinima.successiveMinimum L (k.val + 1) := lt_of_le_of_lt hy_norm h2lt
      have hnreal : (0 : ℝ) < (n (k.val + 1) : ℝ) := by exact_mod_cast hnk1
      rw [hyl_eq] at hylt
      exact lt_of_mul_lt_mul_left hylt (le_of_lt hnreal)
    -- interior exclusion: w is in the span of the first k.val flag vectors
    have hw_span_v : (w : E) ∈ Submodule.span ℝ
        {x : E | ∃ j : Fin d, j.val < k.val ∧ x = (v j : E)} := by
      have hie := Commons.Lattice.SuccessiveMinima.interior_exclusion L hfin v hvlin hvbd
        (k.val + 1) (by omega) (by omega) w hw_norm
      simpa using hie
    -- w has a nonzero k-th coordinate but lies in the span of the earlier flag vectors
    have hw_span_b : (w : E) ∈ Submodule.span ℝ
        {x : E | ∃ j : Fin d, j.val < k.val ∧ x = (b j : E)} := by
      by_cases hk0 : k.val = 0
      · -- empty span: (w : E) = 0, still an element of the b-span
        have hmem0 := hw_span_v
        have hspan0 : Submodule.span ℝ
            {x : E | ∃ j : Fin d, j.val < k.val ∧ x = (v j : E)} = ⊥ := by
          simp [hk0]
        have hz : (w : E) = 0 := by
          rw [hspan0] at hmem0
          exact (Submodule.mem_bot ℝ).mp hmem0
        rw [hz]
        simp [hk0]
      · -- flag equality between the two prefix spans
        have hk_ge1 : 1 ≤ k.val := by omega
        let k0 : Fin d := ⟨k.val - 1, by omega⟩
        have hkv : k0.val + 1 = k.val := by
          dsimp [k0]
          omega
        have hm' : k0.val + 1 ≤ d := by
          dsimp [k0]
          omega
        have hflag_set : Submodule.span ℝ
              {x : E | ∃ j : Fin d, j.val < k.val ∧ x = (v j : E)} =
            Submodule.span ℝ
              {x : E | ∃ j : Fin d, j.val < k.val ∧ x = (b j : E)} := by
          rw [← hkv]
          calc
            Submodule.span ℝ {x : E | ∃ j : Fin d, j.val < k0.val + 1 ∧ x = (v j : E)}
                = Submodule.span ℝ (Set.range (fun j : Fin (k0.val + 1) => ((v ⟨j.val, by omega⟩ : L) : E))) := by
                  exact (span_prefix_eq_lt (d := d) (m := k0.val + 1) hm' (fun j : Fin d => (v j : E))).symm
            _ = Submodule.span ℝ (Set.range (fun j : Fin (k0.val + 1) => ((b ⟨j.val, by omega⟩ : L) : E))) := by
                  exact (hbflag k0).symm
            _ = Submodule.span ℝ {x : E | ∃ j : Fin d, j.val < k0.val + 1 ∧ x = (b j : E)} :=
                  span_prefix_eq_lt (d := d) (m := k0.val + 1) hm' (fun j : Fin d => (b j : E))
        rw [← hflag_set]
        exact hw_span_v
    -- express the span with the ambient real basis bR instead of (b j : E)
    have hw_span_bR : (w : E) ∈ Submodule.span ℝ
        {x : E | ∃ j : Fin d, j.val < k.val ∧ x = (bR j : E)} := by
      have hset : {x : E | ∃ j : Fin d, j.val < k.val ∧ x = (b j : E)} =
          {x : E | ∃ j : Fin d, j.val < k.val ∧ x = (bR j : E)} := by
        ext x
        constructor <;> rintro ⟨j, hj, rfl⟩ <;> refine ⟨j, hj, ?_⟩ <;> simp [bR]
      rw [← hset]
      exact hw_span_b
    have hcoord_zero : bR.coord k (w : E) = 0 :=
      coord_zero_of_mem_span_lt bR k hw_span_bR
    exact hw_coord_ne hcoord_zero
  -- the codomain is finite and its cardinality is the product of the tower values
  letI : (i : Fin d) → Fintype (ZMod (n (i.val + 1))) := by
    intro i
    letI : NeZero (n (i.val + 1)) := ⟨by
      have hnp := hnpos (i.val + 1) (by omega) (by omega)
      omega⟩
    infer_instance
  have hcard_cod : Nat.card ((i : Fin d) → ZMod (n (i.val + 1))) = ∏ i : Fin d, n (i.val + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro i hi
    simp [ZMod.card]
  have hcount : (Nat.card {v : L // ‖(v : E)‖ ≤ N} : ℕ) ≤
      Nat.card ((i : Fin d) → ZMod (n (i.val + 1))) := by
    exact Nat.card_le_card_of_injective
      (fun x : {v : L // ‖(v : E)‖ ≤ N} => fun i : Fin d =>
        (b.repr x.1 i : ZMod (n (i.val + 1)))) h_φ_inj
  exact le_trans hcount (by rw [hcard_cod])

theorem lattice_count_int {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {d : ℕ} (hfin : Module.finrank ℤ L = d) (hd1 : 1 ≤ d) (N : ℕ) (hN : 1 ≤ N) :
    (Nat.card {v : L // ‖(v : E)‖ ≤ N} : ℕ) ≤
      2 ^ (d - 1) *
        ∏ i : Fin d,
          ((Int.floor ((2 * (N : ℝ)) / Commons.Lattice.SuccessiveMinima.successiveMinimum L (i.val + 1))).toNat + 1) := by
  classical
  let R : ℝ := (N : ℝ)
  let q : ℕ → ℕ := fun k =>
    (Int.floor ((2 * R) / Commons.Lattice.SuccessiveMinima.successiveMinimum L k)).toNat + 1
  -- positivity of the successive minima
  have hmu_pos : ∀ k : ℕ, 1 ≤ k → k ≤ d →
      0 < Commons.Lattice.SuccessiveMinima.successiveMinimum L k := by
    intro k hk1 hkd
    exact Commons.Lattice.SuccessiveMinima.positive L k hk1 (by simpa [hfin] using hkd)
  have hRpos : (0 : ℝ) < R := by
    dsimp [R]
    exact_mod_cast hN
  have hRnonneg : 0 ≤ R := le_of_lt hRpos
  have h2R : (0 : ℝ) ≤ 2 * R := by nlinarith
  -- q ≥ 1
  have hq1 : ∀ k : ℕ, 1 ≤ k → k ≤ d → 1 ≤ q k := by
    intro k hk1 hkd
    dsimp [q]
    omega
  -- q is non-increasing (successive minima are non-decreasing)
  have hmu_mono : ∀ {i j : ℕ}, i ≤ j → j ≤ d →
      Commons.Lattice.SuccessiveMinima.successiveMinimum L i ≤
        Commons.Lattice.SuccessiveMinima.successiveMinimum L j := by
    intro i j hij hj
    exact Commons.Lattice.SuccessiveMinima.successiveMinimum_mono L hij (by simpa [hfin] using hj)
  have hq_mono : ∀ k : ℕ, 1 ≤ k → k < d → q (k + 1) ≤ q k := by
    intro k hk1 hkd
    have hx1 : 0 ≤ (2 * R) / Commons.Lattice.SuccessiveMinima.successiveMinimum L (k + 1) := by
      exact div_nonneg h2R (le_of_lt (hmu_pos (k + 1) (by omega) (by omega)))
    have hx2 : 0 ≤ (2 * R) / Commons.Lattice.SuccessiveMinima.successiveMinimum L k := by
      exact div_nonneg h2R (le_of_lt (hmu_pos k hk1 (by omega)))
    have hle_x : (2 * R) / Commons.Lattice.SuccessiveMinima.successiveMinimum L (k + 1) ≤
        (2 * R) / Commons.Lattice.SuccessiveMinima.successiveMinimum L k := by
      have hle_mu : Commons.Lattice.SuccessiveMinima.successiveMinimum L k ≤
          Commons.Lattice.SuccessiveMinima.successiveMinimum L (k + 1) :=
        hmu_mono (by omega) (by omega)
      -- multiply by the positive denominators: 2R/μ(k+1) ≤ 2R/μ(k)
      have hinv : (1 : ℝ) / Commons.Lattice.SuccessiveMinima.successiveMinimum L (k + 1) ≤
          (1 : ℝ) / Commons.Lattice.SuccessiveMinima.successiveMinimum L k :=
        one_div_le_one_div_of_le (hmu_pos k hk1 (by omega)) hle_mu
      calc
        (2 * R) / Commons.Lattice.SuccessiveMinima.successiveMinimum L (k + 1)
            = (2 * R) * ((1 : ℝ) / Commons.Lattice.SuccessiveMinima.successiveMinimum L (k + 1)) := by
              rw [mul_one_div]
        _ ≤ (2 * R) * ((1 : ℝ) / Commons.Lattice.SuccessiveMinima.successiveMinimum L k) := by
              exact mul_le_mul_of_nonneg_left hinv h2R
        _ = (2 * R) / Commons.Lattice.SuccessiveMinima.successiveMinimum L k := by
              rw [mul_one_div]
    dsimp [q]
    rw [Int.floor_toNat, Int.floor_toNat]
    exact Nat.add_le_add_right (Nat.floor_mono hle_x) 1
  -- q is strictly above 2N/λ
  have hq_gt : ∀ k : ℕ, 1 ≤ k → k ≤ d →
      (2 * R) / Commons.Lattice.SuccessiveMinima.successiveMinimum L k < (q k : ℝ) := by
    intro k hk1 hkd
    dsimp [q]
    rw [Int.floor_toNat]
    -- (q k : ℝ) = (Nat.floor x : ℝ) + 1
    have hx0 : 0 ≤ (2 * R) / Commons.Lattice.SuccessiveMinima.successiveMinimum L k :=
      div_nonneg h2R (le_of_lt (hmu_pos k hk1 hkd))
    have hlt := Nat.lt_floor_add_one ((2 * R) / Commons.Lattice.SuccessiveMinima.successiveMinimum L k)
    simpa using hlt
  -- build the tower
  rcases Commons.Lattice.Counting.divisibility_tower d hd1 q hq1 hq_mono with ⟨n, hn_top, hn_bound, hn_dvd⟩
  -- count
  have hcount := lattice_count_int_tower L hfin hd1 N hN q hq1 hq_mono hq_gt n hn_top hn_bound hn_dvd
  have hprod : (∏ i : Fin d, n (i.val + 1)) ≤ 2 ^ (d - 1) * ∏ i : Fin d, q (i.val + 1) :=
    prod_tower_le_prod_q hd1 q n hn_top (fun k hk1 hkd => (hn_bound k hk1 hkd).2)
  have hfinal : (Nat.card {v : L // ‖(v : E)‖ ≤ N} : ℕ) ≤
      2 ^ (d - 1) * ∏ i : Fin d, q (i.val + 1) := by
    exact le_trans hcount hprod
  -- the product of q's is exactly the claimed product
  convert hfinal using 2 <;> ext i <;> rfl

end Commons.Lattice.Counting
