import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.box_card
import Submission.Work.HP.ESL.slab_ball_ncard
import Submission.Work.HP.MDEstimates.rk_projScale
import Submission.Work.HP.EEupper.exists_int_reduce_dot
import Submission.Work.HP.ESL.detL_span_pair_sq
import Submission.Work.HP.FM.minkowski_lower
import Submission.Work.HP.FM3.dmin_two_singleton_le
import Submission.Work.HP.FM3.ballCount_two_le
import Submission.Work.HP.FM3.dyadic_sum_bound

/-!
# `Work.HP.FM3.ell_two_count_free`

The paper's Lemma `ℓ_r(X)` (Browning–Le Boudec–Sawin, §3.3) for `r = 2`:

`#{x ∈ ℤ^{n+1} : x ≠ 0, ‖x‖ ≤ X, 𝔡₂(x) ≤ Δ} ≪ X² Δⁿ log(2Δ)`.

Each `x` with `𝔡₂(x) ≤ Δ` lies in a primitive rank-two lattice `L` with `detL L ≤ Δ + 1`
(`dmin_two_singleton_le`), and the number of points of `L` of norm `≤ X` is `≪ X²/λ₁(L)²`
(`ballCount_two_le`).  Lattices are grouped by the dyadic window of their successive minima; the
windows count `≪ 2^{k₁n} 2^{k₂(n+2)}` (`num_lattices_two`) and only windows with
`2^{k₁+k₂} ≤ 8(Δ+1)` occur because `λ₁λ₂ ≤ 2 detL L` (`lam_two_mul_le_detL`).  The remaining
dyadic sum is `≪ Δⁿ log(2Δ)` (`dyadic_sum_bound`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.FM3

/-- For a sublattice `L ⊆ ℤ^ι`, `1 ≤ λ_j` for `1 ≤ j ≤ rk L`. -/
lemma one_le_lam {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ))
    {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ rk L) : 1 ≤ lam L j := by
  obtain ⟨g, hgL, hgI⟩ := exists_linIndep_card L hjk
  have hne : (lamSet L j).Nonempty :=
    ⟨∑ i, eNorm (g i), Finset.sum_nonneg (fun i _ => eNorm_nonneg _), g, hgL, hgI,
      fun i => Finset.single_le_sum (fun k _ => eNorm_nonneg _) (Finset.mem_univ i)⟩
  rw [lam_eq_sInf L j]
  refine le_csInf hne ?_
  rintro r ⟨hr0, f, hfL, hfI, hfr⟩
  exact le_trans (one_le_eNorm_of_ne_zero (hfI.ne_zero ⟨0, by omega⟩)) (hfr ⟨0, by omega⟩)

/-- The dyadic window exponent dominates the corresponding successive minimum. -/
lemma lam_le_two_pow_kwin {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (L : Submodule ℤ (ι → ℤ)) (j : Fin r) (hpos : 0 < lam L (j.1 + 1)) :
    lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin r L j) := by
  have h1 : Real.logb 2 (lam L (j.1 + 1)) ≤ ((kwin r L j : ℕ) : ℝ) := Nat.le_ceil _
  have h3 : (2 : ℝ) ^ (Real.logb 2 (lam L (j.1 + 1))) ≤ (2 : ℝ) ^ ((kwin r L j : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  rw [Real.rpow_logb (by norm_num) (by norm_num) hpos, Real.rpow_natCast] at h3
  exact h3

/-- The dyadic window exponent is at most twice the corresponding successive minimum. -/
lemma two_pow_kwin_le {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (L : Submodule ℤ (ι → ℤ)) (j : Fin r) (h1 : 1 ≤ lam L (j.1 + 1)) :
    (2 : ℝ) ^ (kwin r L j) ≤ 2 * lam L (j.1 + 1) := by
  have hlog0 : (0 : ℝ) ≤ Real.logb 2 (lam L (j.1 + 1)) :=
    Real.logb_nonneg (by norm_num) h1
  have h2 : ((kwin r L j : ℕ) : ℝ) < Real.logb 2 (lam L (j.1 + 1)) + 1 :=
    Nat.ceil_lt_add_one hlog0
  have h3 : (2 : ℝ) ^ ((kwin r L j : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ (Real.logb 2 (lam L (j.1 + 1)) + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt h2)
  rw [Real.rpow_natCast, Real.rpow_add (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (lt_of_lt_of_le zero_lt_one h1),
    Real.rpow_one] at h3
  linarith

/-- The real inner product `dotR` of `toR`-vectors is the cast of the integral pairing. -/
lemma dotR_toR_eq_dotZ_fm3 {ι : Type*} [Fintype ι] (v w : ι → ℤ) :
    dotR (toR v) (toR w) = ((dotZ v w : ℤ) : ℝ) := by
  simp only [dotR, toR, dotZ, Int.cast_sum, Int.cast_mul]

/-- **A reduced basis partner for a shortest vector.**  For a rank-two lattice `L` and a shortest
nonzero vector `u ∈ L`, there is `w ∈ L` with `span_ℤ{u,w} = L` and `2|⟨w,u⟩| ≤ ‖u‖²`.

The proof: `u` is primitive in `L` (else it would be a nontrivial multiple of a shorter vector), so
in a `ℤ`-basis `(b₀,b₁)` of `L` its coordinates `(p,q)` are coprime.  Bézout gives `ps - qr = 1`,
and `w₀ = r b₀ + s b₁` then satisfies `b₀ = s u - q w₀`, `b₁ = -r u + p w₀`, whence
`span{u,w₀} = L`.  Finally `w₀` is shifted by a multiple of `u` to make `|⟨w,u⟩| ≤ ‖u‖²/2`. -/
theorem reduced_partner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (hrk : rk L = 2) (u : ι → ℤ) (hu : u ∈ L) (hu0 : u ≠ 0)
    (hmin : ∀ z : ι → ℤ, z ∈ L → z ≠ 0 → eNorm u ≤ eNorm z) :
    ∃ w : ι → ℤ, w ∈ L ∧ Submodule.span ℤ (Set.range ![u, w]) = L ∧
      |((dotZ w u : ℤ) : ℝ)| ≤ ((dotZ u u : ℤ) : ℝ) / 2 := by
  classical
  obtain ⟨k, bk⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L
  have hk : k = 2 := by
    have h1 : Module.finrank ℤ L = k := by
      rw [Module.finrank_eq_card_basis bk, Fintype.card_fin]
    have h2 : Module.finrank ℤ L = rk L := rfl
    omega
  let b : Module.Basis (Fin 2) ℤ L := bk.reindex (finCongr hk)
  set b0 : ι → ℤ := ((b 0 : L) : ι → ℤ) with hb0
  set b1 : ι → ℤ := ((b 1 : L) : ι → ℤ) with hb1
  have hb0L : b0 ∈ L := (b 0).2
  have hb1L : b1 ∈ L := (b 1).2
  set p : ℤ := b.repr ⟨u, hu⟩ 0 with hp
  set q : ℤ := b.repr ⟨u, hu⟩ 1 with hq
  have huv : p • b0 + q • b1 = u := by
    have h := b.sum_repr ⟨u, hu⟩
    rw [Fin.sum_univ_two] at h
    have hv := congrArg (fun x : L => (x : ι → ℤ)) h
    simpa [hp, hq, hb0, hb1] using hv
  have hgcd : p.gcd q = 1 := by
    by_contra hne
    have hge2 : 2 ≤ p.gcd q := by
      have hpos : 0 < p.gcd q := by
        rcases Nat.eq_zero_or_pos (p.gcd q) with h0 | h0
        · exfalso
          have hpq := Int.gcd_eq_zero_iff.mp h0
          apply hu0
          rw [← huv, hpq.1, hpq.2, zero_smul, zero_smul, add_zero]
        · exact h0
      omega
    set d : ℤ := (p.gcd q : ℤ) with hd
    have hd2 : 2 ≤ d := by rw [hd]; exact_mod_cast hge2
    have hdp : d ∣ p := by rw [hd]; exact Int.gcd_dvd_left p q
    have hdq : d ∣ q := by rw [hd]; exact Int.gcd_dvd_right p q
    set z : ι → ℤ := (p / d) • b0 + (q / d) • b1 with hz
    have hzL : z ∈ L := by
      rw [hz]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hb0L) (Submodule.smul_mem _ _ hb1L)
    have huz : d • z = u := by
      rw [hz, ← huv, smul_add, smul_smul, smul_smul, Int.mul_ediv_cancel' hdp,
        Int.mul_ediv_cancel' hdq]
    have hz0 : z ≠ 0 := by
      intro hz00
      apply hu0
      rw [← huz, hz00, smul_zero]
    have hle := hmin z hzL hz0
    have hzpos : 0 < eNorm z := eNorm_pos_of_ne_zero hz0
    have hdabs : |(d : ℝ)| = (d : ℝ) := by
      rw [abs_of_nonneg]
      exact_mod_cast (by omega : (0 : ℤ) ≤ d)
    have hnorm : eNorm u = |(d : ℝ)| * eNorm z := by
      rw [← huz, MDEstimates.eNorm_smul_int]
    rw [hnorm, hdabs] at hle
    have hd2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    nlinarith [hle, hzpos, hd2R]
  have hbez : ∃ r s : ℤ, p * s - q * r = 1 := by
    have h1 : ((p.gcd q : ℕ) : ℤ) = p * p.gcdA q + q * p.gcdB q := Int.gcd_eq_gcd_ab p q
    rw [hgcd] at h1
    norm_num at h1
    exact ⟨-p.gcdB q, p.gcdA q, by linarith⟩
  obtain ⟨r, s, hrs⟩ := hbez
  set w0 : ι → ℤ := r • b0 + s • b1 with hw0
  have hw0L : w0 ∈ L := by
    rw [hw0]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hb0L) (Submodule.smul_mem _ _ hb1L)
  have hb0' : b0 = s • u - q • w0 := by
    have h1 : s • u - q • w0 = (s * p - q * r) • b0 + (s * q - q * s) • b1 := by
      rw [← huv, hw0]
      module
    rw [h1]
    rw [show s * p - q * r = 1 by linarith [hrs], show s * q - q * s = 0 by ring]
    module
  have hb1' : b1 = (-r) • u + p • w0 := by
    have h1 : (-r) • u + p • w0 = (p * s - q * r) • b1 := by
      rw [← huv, hw0]
      module
    rw [h1, hrs]
    module
  have range_pair : ∀ a c : ι → ℤ, Set.range ![a, c] = ({a, c} : Set (ι → ℤ)) := by
    intro a c
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro hx
      rcases hx with h | h
      · exact ⟨0, by rw [h]; simp⟩
      · exact ⟨1, by rw [h]; simp⟩
  have hspan : Submodule.span ℤ (Set.range ![u, w0]) = L := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le, range_pair]
      intro x hx
      rcases hx with h | h
      · rw [h]; exact hu
      · rw [h]; exact hw0L
    · intro z hz
      have hzrepr : (b.repr ⟨z, hz⟩ 0) • b0 + (b.repr ⟨z, hz⟩ 1) • b1 = z := by
        have h := b.sum_repr ⟨z, hz⟩
        rw [Fin.sum_univ_two] at h
        have hv := congrArg (fun x : L => (x : ι → ℤ)) h
        simpa [hb0, hb1] using hv
      rw [← hzrepr, hb0', hb1', range_pair]
      refine Submodule.add_mem _ ?_ ?_
      · refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
        · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
        · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_)
        · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
        · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  obtain ⟨k', hk'⟩ := EEupper.exists_int_reduce_dot u w0 hu0
  refine ⟨w0 - k' • u, Submodule.sub_mem _ hw0L (Submodule.smul_mem _ _ hu), ?_, ?_⟩
  · have hspan2 : Submodule.span ℤ (Set.range ![u, w0 - k' • u]) = L := by
      refine le_antisymm ?_ ?_
      · rw [Submodule.span_le, range_pair]
        intro x hx
        rcases hx with h | h
        · rw [h]; exact hu
        · rw [h]; exact Submodule.sub_mem _ hw0L (Submodule.smul_mem _ _ hu)
      · intro z hz
        rw [range_pair]
        have hsub : ({u, w0} : Set (ι → ℤ))
            ⊆ (Submodule.span ℤ ({u, w0 - k' • u} : Set (ι → ℤ)) : Set (ι → ℤ)) := by
          intro x hx
          rcases hx with h | h
          · rw [h]; exact Submodule.subset_span (by simp)
          · rw [h, (sub_add_cancel w0 (k' • u)).symm]
            exact Submodule.add_mem _ (Submodule.subset_span (by simp))
              (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        exact (Submodule.span_le.mpr hsub) (by rw [← range_pair u w0, hspan]; exact hz)
    rw [hspan2]
  · have hk2 : 2 * |dotR (toR u) (toR (w0 - k' • u))| ≤ eNorm u ^ 2 := by linarith [hk']
    rw [dotR_toR_eq_dotZ_fm3, eNorm_sq_eq] at hk2
    rw [dotZ_comm (w0 - k' • u) u]
    linarith

/-- A sublattice of rank `≥ 1` has a shortest nonzero vector, whose norm is `λ₁ = lam L 1`. -/
lemma exists_shortest_vec {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ))
    (hrk : 1 ≤ rk L) :
    ∃ u : ι → ℤ, u ∈ L ∧ u ≠ 0 ∧ eNorm u = lam L 1 := by
  classical
  obtain ⟨g, hgL, hgI⟩ := exists_linIndep_card L hrk
  have hne : (lamSet L 1).Nonempty :=
    ⟨eNorm (g 0), eNorm_nonneg _, g, hgL, hgI, fun i => by
      have hi : i = 0 := Subsingleton.elim i 0
      rw [hi]⟩
  have hρ : lam L 1 < lam L 1 + 1 := by linarith
  obtain ⟨f, hfL, hfI, hfb⟩ := lam_witness L hrk (i := 1) (ρ := lam L 1 + 1) hρ
  have hfin : ({v : ι → ℤ | v ∈ L ∧ v ≠ 0 ∧ eNorm v ≤ lam L 1 + 1} : Set (ι → ℤ)).Finite :=
    (MDBasic.finite_eNorm_le (lam L 1 + 1)).subset (fun v hv => hv.2.2)
  have hne2 : ({v : ι → ℤ | v ∈ L ∧ v ≠ 0 ∧ eNorm v ≤ lam L 1 + 1} : Set (ι → ℤ)).Nonempty :=
    ⟨f 0, hfL 0, hfI.ne_zero 0, hfb 0⟩
  obtain ⟨u, huT, hmin⟩ := Set.exists_min_image _ eNorm hfin hne2
  have huL : u ∈ L := huT.1
  have hu0 : u ≠ 0 := huT.2.1
  have huup : eNorm u ≤ lam L 1 + 1 := huT.2.2
  have hlow : lam L 1 ≤ eNorm u := lam_one_le_eNorm L huL hu0
  have hup : eNorm u ≤ lam L 1 := by
    by_contra hcon
    have hlt : lam L 1 < eNorm u := not_le.mp hcon
    rw [lam_eq_sInf L 1] at hlt
    obtain ⟨s, hsS, hsu⟩ := exists_lt_of_csInf_lt hne hlt
    obtain ⟨hr0, f', hf'L, hf'I, hf'b⟩ := hsS
    have h1 : eNorm (f' 0) ≤ s := hf'b 0
    have h2 : eNorm (f' 0) < eNorm u := lt_of_le_of_lt h1 hsu
    have h3 : eNorm (f' 0) ≤ lam L 1 + 1 := by linarith
    have := hmin (f' 0) ⟨hf'L 0, hf'I.ne_zero 0, h3⟩
    linarith
  exact ⟨u, huL, hu0, le_antisymm hup hlow⟩

/-- **Minkowski's second theorem in rank two, elementary form.**  For a rank-two integral lattice,
`λ₁(L)·λ₂(L) ≤ 2 detL L`. -/
theorem lam_two_mul_le_detL_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (hrk : rk L = 2) :
    lam L 1 * lam L 2 ≤ 2 * detL L := by
  classical
  obtain ⟨u, huL, hu0, hueq⟩ := exists_shortest_vec L (by omega : 1 ≤ rk L)
  have hmin : ∀ z : ι → ℤ, z ∈ L → z ≠ 0 → eNorm u ≤ eNorm z := by
    intro z hz hz0
    rw [hueq]
    exact lam_one_le_eNorm L hz hz0
  obtain ⟨w, hwL, hspan, hdot⟩ := reduced_partner L hrk u huL hu0 hmin
  have hli : LinearIndependent ℤ ![u, w] := by
    rw [linearIndependent_iff_card_le_finrank_span]
    have hfin : Set.finrank ℤ (Set.range ![u, w]) = rk L := by
      change Module.finrank ℤ ↥(Submodule.span ℤ (Set.range ![u, w])) = rk L
      rw [hspan, rk]
    rw [hfin, hrk]
    simp
  have hw0 : w ≠ 0 := by
    have h := hli.ne_zero (1 : Fin 2)
    simpa using h
  have huw : eNorm u ≤ eNorm w := hmin w hwL hw0
  have hlam1 : lam L 1 = eNorm u := hueq.symm
  have hlam2 : lam L 2 ≤ eNorm w :=
    (lam_two_le_max L huL hwL hli).trans (le_of_eq (max_eq_right huw))
  have hdet2 : detL L ^ 2 = eNorm u ^ 2 * eNorm w ^ 2 - ((dotZ w u : ℤ) : ℝ) ^ 2 := by
    have hset : ({u, w} : Set (ι → ℤ)) = Set.range ![u, w] := by
      ext z; simp [or_comm]
    have h := ESL.detL_span_pair_sq u w hli
    rw [hset, dotZ_comm u w] at h
    rwa [hspan] at h
  have ha2 : ((dotZ w u : ℤ) : ℝ) ^ 2 ≤ eNorm u ^ 4 / 4 := by
    have huu : ((dotZ u u : ℤ) : ℝ) = eNorm u ^ 2 := (eNorm_sq_eq u).symm
    have h1 : |((dotZ w u : ℤ) : ℝ)| ≤ |eNorm u ^ 2 / 2| := by
      rw [abs_of_nonneg (div_nonneg (sq_nonneg (eNorm u)) (by norm_num : (0 : ℝ) ≤ 2))]
      rw [huu] at hdot
      exact hdot
    have h2 : ((dotZ w u : ℤ) : ℝ) ^ 2 ≤ (eNorm u ^ 2 / 2) ^ 2 := sq_le_sq.mpr h1
    calc ((dotZ w u : ℤ) : ℝ) ^ 2 ≤ (eNorm u ^ 2 / 2) ^ 2 := h2
      _ = eNorm u ^ 4 / 4 := by ring
  have hlsq : eNorm u ^ 2 ≤ eNorm w ^ 2 := by
    nlinarith [huw, eNorm_nonneg u, eNorm_nonneg w]
  have hlam4 : eNorm u ^ 4 ≤ eNorm u ^ 2 * eNorm w ^ 2 := by
    have := mul_le_mul_of_nonneg_left hlsq (sq_nonneg (eNorm u))
    nlinarith [this]
  have h4a2 : 4 * ((dotZ w u : ℤ) : ℝ) ^ 2 ≤ eNorm u ^ 4 := by linarith [ha2]
  have h3 : 4 * ((dotZ w u : ℤ) : ℝ) ^ 2
      ≤ 3 * (eNorm u ^ 2 * eNorm w ^ 2) := by
    have hnn : 0 ≤ eNorm u ^ 2 * eNorm w ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith [h4a2, hlam4, hnn]
  have hkey : (eNorm u * eNorm w) ^ 2 ≤ (2 * detL L) ^ 2 := by
    have hsq : (eNorm u * eNorm w) ^ 2 = eNorm u ^ 2 * eNorm w ^ 2 := by ring
    have hexp : (2 * detL L) ^ 2 = 4 * detL L ^ 2 := by ring
    rw [hsq, hexp, hdet2]
    linarith [h3]
  have hmain : eNorm u * eNorm w ≤ 2 * detL L := by
    have h := sq_le_sq.mp hkey
    rw [abs_of_nonneg (mul_nonneg (eNorm_nonneg u) (eNorm_nonneg w)),
      abs_of_nonneg (by linarith [detL_nonneg L])] at h
    exact h
  calc lam L 1 * lam L 2 = eNorm u * lam L 2 := by rw [hlam1]
    _ ≤ eNorm u * eNorm w := mul_le_mul_of_nonneg_left hlam2 (eNorm_nonneg u)
    _ ≤ 2 * detL L := hmain

/-- **Assembly for `ℓ_{2,n}(X;Δ)`**: all four analytic inputs are hypotheses. -/
theorem ell_two_count_aux (n : ℕ) (hn : 2 ≤ n)
    (hD : ∀ (x : Fin (n + 1) → ℤ) (D : ℝ), x ≠ 0 → dmin 2 {x} ≤ D →
      ∃ L : Submodule ℤ (Fin (n + 1) → ℤ),
        IsPrimLat L ∧ rk L = 2 ∧ x ∈ L ∧ detL L ≤ D + 1)
    (KC : ℝ) (hKCpos : 0 < KC)
    (hC : ∀ (s : Fin 2 → ℝ) (F : Finset (Submodule ℤ (Fin (n + 1) → ℤ))),
      (∀ j, 1 ≤ s j) →
      (∀ L ∈ F, IsPrimLat L ∧ rk L = 2 ∧ ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j) →
      (F.card : ℝ) ≤ KC * s 0 ^ (n + 2) * s 1 ^ n)
    (hA : ∀ L : Submodule ℤ (Fin (n + 1) → ℤ), rk L = 2 → lam L 1 * lam L 2 ≤ 2 * detL L)
    (KB : ℝ) (hKBpos : 0 < KB)
    (hB : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (X : ℝ), rk L = 2 → 1 ≤ X → lam L 1 ≤ X →
      (ballCount L X : ℝ) ≤ KB * X ^ 2 / lam L 1 ^ 2)
    (KD : ℝ) (hKDpos : 0 < KD)
    (hDy : ∀ (Δ : ℝ) (A : Finset (ℕ × ℕ)), 1 ≤ Δ →
      (∀ k ∈ A, (2 : ℝ) ^ (k.1 + k.2) ≤ 8 * (Δ + 1)) →
      (∑ k ∈ A, (2 : ℝ) ^ (n * (k.1 + k.2))) ≤ KD * Δ ^ n * Real.log (2 * Δ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ X Δ : ℝ, 1 ≤ X → 1 ≤ Δ →
      (({x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ X ∧ dmin 2 {x} ≤ Δ}).ncard : ℝ)
        ≤ K * X ^ 2 * Δ ^ n * Real.log (2 * Δ) := by
  classical
  refine ⟨4 * KB * KC * KD, by positivity, ?_⟩
  intro X Δ hX hΔ
  set S : Set (Fin (n + 1) → ℤ) := {x | x ≠ 0 ∧ eNorm x ≤ X ∧ dmin 2 {x} ≤ Δ} with hSdef
  have hSmem : ∀ x : Fin (n + 1) → ℤ,
      (x ∈ S ↔ (x ≠ 0 ∧ eNorm x ≤ X ∧ dmin 2 {x} ≤ Δ)) := by
    intro x
    rw [hSdef]
    exact Iff.rfl
  have hSfin : S.Finite :=
    (MDBasic.finite_eNorm_le X).subset (fun x hx => ((hSmem x).mp hx).2.1)
  have hchoice : ∀ x ∈ S, ∃ L : Submodule ℤ (Fin (n + 1) → ℤ),
      IsPrimLat L ∧ rk L = 2 ∧ x ∈ L ∧ detL L ≤ Δ + 1 := by
    intro x hx
    exact hD x Δ ((hSmem x).mp hx).1 ((hSmem x).mp hx).2.2
  let Lf : (Fin (n + 1) → ℤ) → Submodule ℤ (Fin (n + 1) → ℤ) := fun x =>
    if h : x ∈ S then Classical.choose (hchoice x h) else ⊥
  have hLf : ∀ x ∈ S, IsPrimLat (Lf x) ∧ rk (Lf x) = 2 ∧ x ∈ Lf x ∧ detL (Lf x) ≤ Δ + 1 := by
    intro x hx
    simp only [Lf, dif_pos hx]
    exact Classical.choose_spec (hchoice x hx)
  set F : Finset (Submodule ℤ (Fin (n + 1) → ℤ)) := hSfin.toFinset.image Lf with hFdef
  -- data of a lattice in `F`, recovered from its witnessing point
  have hLdata : ∀ L ∈ F, IsPrimLat L ∧ rk L = 2 ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ X := by
    intro L hL
    rw [hFdef, Finset.mem_image] at hL
    obtain ⟨x, hxT, rfl⟩ := hL
    have hxS : x ∈ S := by rwa [Set.Finite.mem_toFinset] at hxT
    obtain ⟨hp, hr, hxmem, hdet⟩ := hLf x hxS
    have hxne : x ≠ 0 := ((hSmem x).mp hxS).1
    have hxX : eNorm x ≤ X := ((hSmem x).mp hxS).2.1
    exact ⟨hp, hr, hdet, le_trans (lam_one_le_eNorm (Lf x) hxmem hxne) hxX⟩
  -- Step 1: `#S ≤ ∑_{L ∈ F} #(L ∩ B(X))`.
  have hfib : ∀ L ∈ F, (((hSfin.toFinset).filter (fun x => Lf x = L)).card : ℝ)
      ≤ (ballCount L X : ℝ) := by
    intro L hL
    have hfin2 : ({v : Fin (n + 1) → ℤ | v ∈ L ∧ eNorm v ≤ X} : Set _).Finite :=
      (MDBasic.finite_eNorm_le X).subset (fun v hv => hv.2)
    have hsub : ∀ x ∈ (hSfin.toFinset).filter (fun x => Lf x = L), x ∈ L ∧ eNorm x ≤ X := by
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hxT, hxL⟩ := hx
      have hxS : x ∈ S := by rwa [Set.Finite.mem_toFinset] at hxT
      have hxmem : x ∈ Lf x := (hLf x hxS).2.2.1
      exact ⟨hxL ▸ hxmem, ((hSmem x).mp hxS).2.1⟩
    have h1 : (((hSfin.toFinset).filter (fun x => Lf x = L)) : Set _).ncard
        ≤ ({v : Fin (n + 1) → ℤ | v ∈ L ∧ eNorm v ≤ X} : Set _).ncard :=
      Set.ncard_le_ncard (fun x hx => hsub x hx) hfin2
    rw [Set.ncard_coe_finset] at h1
    show (((hSfin.toFinset).filter (fun x => Lf x = L)).card : ℝ)
      ≤ (({v : Fin (n + 1) → ℤ | v ∈ L ∧ eNorm v ≤ X} : Set _).ncard : ℝ)
    exact_mod_cast h1
  have hstep1 : ((S.ncard : ℕ) : ℝ) ≤ ∑ L ∈ F, (ballCount L X : ℝ) := by
    have hmap : (hSfin.toFinset : Set (Fin (n + 1) → ℤ)).MapsTo Lf F := by
      intro x hx
      rw [hFdef]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hcard : ((S.ncard : ℕ) : ℝ)
        = ∑ L ∈ F, (((hSfin.toFinset).filter (fun x => Lf x = L)).card : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hSfin, Finset.card_eq_sum_card_fiberwise hmap]
      push_cast
      rfl
    rw [hcard]
    exact Finset.sum_le_sum hfib
  -- Step 2: the dyadic window decomposition.
  let kf : Submodule ℤ (Fin (n + 1) → ℤ) → ℕ × ℕ := fun L => (kwin 2 L 0, kwin 2 L 1)
  set Kx : Finset (ℕ × ℕ) := F.image kf with hKxdef
  have hkf_mem : ∀ L ∈ F, kf L ∈ Kx := by
    intro L hL
    rw [hKxdef]
    exact Finset.mem_image.mpr ⟨L, hL, rfl⟩
  -- ball count at the window scale
  have hballwin : ∀ (k : ℕ × ℕ) (L : Submodule ℤ (Fin (n + 1) → ℤ)),
      L ∈ F → kf L = k →
      (ballCount L X : ℝ) ≤ 4 * KB * X ^ 2 / ((2 : ℝ) ^ (k.1)) ^ 2 := by
    intro k L hL hkL
    obtain ⟨-, hrk, -, hlX⟩ := hLdata L hL
    have hb := hB L X hrk hX hlX
    have hge1 : 1 ≤ lam L 1 := one_le_lam L le_rfl (by rw [hrk]; norm_num)
    have htw : (2 : ℝ) ^ (kwin 2 L 0) ≤ 2 * lam L 1 :=
      two_pow_kwin_le L 0 (by simpa using hge1)
    have hk1 : kwin 2 L 0 = k.1 := congrArg Prod.fst hkL
    have hpos : 0 < lam L 1 := lam_pos L le_rfl (by rw [hrk]; norm_num)
    have hsq : ((2 : ℝ) ^ (k.1)) ^ 2 ≤ 4 * (lam L 1) ^ 2 := by
      rw [← hk1]
      have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ (kwin 2 L 0) := by positivity
      calc ((2 : ℝ) ^ (kwin 2 L 0)) ^ 2 ≤ (2 * lam L 1) ^ 2 := pow_le_pow_left₀ h0 htw 2
        _ = 4 * (lam L 1) ^ 2 := by ring
    have hKBX : 0 ≤ KB * X ^ 2 := by positivity
    have hmain : KB * X ^ 2 / (lam L 1) ^ 2 ≤ 4 * KB * X ^ 2 / ((2 : ℝ) ^ (k.1)) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc KB * X ^ 2 * ((2 : ℝ) ^ (k.1)) ^ 2
          ≤ KB * X ^ 2 * (4 * (lam L 1) ^ 2) := mul_le_mul_of_nonneg_left hsq hKBX
        _ = 4 * KB * X ^ 2 * (lam L 1) ^ 2 := by ring
    calc (ballCount L X : ℝ) ≤ KB * X ^ 2 / (lam L 1) ^ 2 := hb
      _ ≤ 4 * KB * X ^ 2 / ((2 : ℝ) ^ (k.1)) ^ 2 := hmain
  -- number of lattices in a window
  have hcardwin : ∀ k ∈ Kx,
      (((F.filter (fun L => kf L = k)).card : ℕ) : ℝ)
        ≤ KC * ((2 : ℝ) ^ (k.1)) ^ (n + 2) * ((2 : ℝ) ^ (k.2)) ^ n := by
    intro k hk
    set s : Fin 2 → ℝ := ![(2 : ℝ) ^ (k.1), (2 : ℝ) ^ (k.2)] with hsdef
    have hs1 : ∀ j, 1 ≤ s j := by
      intro j
      have h0 : (1 : ℝ) ≤ (2 : ℝ) ^ (k.1) := one_le_pow₀ (by norm_num)
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k.2) := one_le_pow₀ (by norm_num)
      fin_cases j
      · simpa [hsdef] using h0
      · simpa [hsdef] using h1
    have hs0 : s 0 = (2 : ℝ) ^ (k.1) := by simp [hsdef]
    have hs1' : s 1 = (2 : ℝ) ^ (k.2) := by simp [hsdef]
    have hgood : ∀ L ∈ F.filter (fun L => kf L = k),
        IsPrimLat L ∧ rk L = 2 ∧ ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j := by
      intro L hL
      rw [Finset.mem_filter] at hL
      obtain ⟨hLF, hkL⟩ := hL
      obtain ⟨hp, hr, -, -⟩ := hLdata L hLF
      refine ⟨hp, hr, ?_⟩
      intro j
      have hk0 : kwin 2 L 0 = k.1 := congrArg Prod.fst hkL
      have hk1 : kwin 2 L 1 = k.2 := congrArg Prod.snd hkL
      have hjle : j.1 + 1 ≤ rk L := by rw [hr]; omega
      have hge1 : 1 ≤ lam L (j.1 + 1) := one_le_lam L (by omega) hjle
      have hpos : 0 < lam L (j.1 + 1) := lt_of_lt_of_le zero_lt_one hge1
      have hle := lam_le_two_pow_kwin L j hpos
      fin_cases j
      · simpa [hk0, hsdef] using hle
      · simpa [hk1, hs1'] using hle
    have hres := hC s (F.filter (fun L => kf L = k)) hs1 hgood
    rw [hs0, hs1'] at hres
    exact hres
  -- the class bound
  have hclass : ∀ k ∈ Kx, (∑ L ∈ F.filter (fun L => kf L = k), (ballCount L X : ℝ))
      ≤ 4 * KB * KC * X ^ 2 * (2 : ℝ) ^ (n * (k.1 + k.2)) := by
    intro k hk
    have hstep : (∑ L ∈ F.filter (fun L => kf L = k), (ballCount L X : ℝ))
        ≤ ∑ _L ∈ F.filter (fun L => kf L = k),
            (4 * KB * X ^ 2 / ((2 : ℝ) ^ (k.1)) ^ 2) := by
      refine Finset.sum_le_sum ?_
      intro L hL
      rw [Finset.mem_filter] at hL
      exact hballwin k L hL.1 hL.2
    have hconst : (∑ _L ∈ F.filter (fun L => kf L = k),
            (4 * KB * X ^ 2 / ((2 : ℝ) ^ (k.1)) ^ 2))
        = (((F.filter (fun L => kf L = k)).card : ℕ) : ℝ)
            * (4 * KB * X ^ 2 / ((2 : ℝ) ^ (k.1)) ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcnn : 0 ≤ 4 * KB * X ^ 2 / ((2 : ℝ) ^ (k.1)) ^ 2 := by positivity
    calc (∑ L ∈ F.filter (fun L => kf L = k), (ballCount L X : ℝ))
        ≤ ∑ _L ∈ F.filter (fun L => kf L = k),
            (4 * KB * X ^ 2 / ((2 : ℝ) ^ (k.1)) ^ 2) := hstep
      _ = (((F.filter (fun L => kf L = k)).card : ℕ) : ℝ)
            * (4 * KB * X ^ 2 / ((2 : ℝ) ^ (k.1)) ^ 2) := hconst
      _ ≤ (KC * ((2 : ℝ) ^ (k.1)) ^ (n + 2) * ((2 : ℝ) ^ (k.2)) ^ n)
            * (4 * KB * X ^ 2 / ((2 : ℝ) ^ (k.1)) ^ 2) :=
          mul_le_mul_of_nonneg_right (hcardwin k hk) hcnn
      _ = 4 * KB * KC * X ^ 2 * (2 : ℝ) ^ (n * (k.1 + k.2)) := by
          have hp : (2 : ℝ) ^ (n * (k.1 + k.2))
              = ((2 : ℝ) ^ (k.1)) ^ n * ((2 : ℝ) ^ (k.2)) ^ n := by
            rw [mul_comm n (k.1 + k.2), pow_mul, pow_add, mul_pow]
          have hpow : ((2 : ℝ) ^ (k.1)) ^ (n + 2)
              = ((2 : ℝ) ^ (k.1)) ^ n * ((2 : ℝ) ^ (k.1)) ^ 2 := pow_add _ n 2
          rw [hp, hpow]
          field_simp
  -- the dyadic window constraint
  have hcons : ∀ k ∈ Kx, (2 : ℝ) ^ (k.1 + k.2) ≤ 8 * (Δ + 1) := by
    intro k hk
    rw [hKxdef, Finset.mem_image] at hk
    obtain ⟨L, hL, rfl⟩ := hk
    obtain ⟨-, hrk, hdet, -⟩ := hLdata L hL
    have hge1 : 1 ≤ lam L 1 := one_le_lam L le_rfl (by omega)
    have hge2 : 1 ≤ lam L 2 := one_le_lam L (by norm_num) (by omega)
    have h1 : (2 : ℝ) ^ (kwin 2 L 0) ≤ 2 * lam L 1 := two_pow_kwin_le L 0 (by simpa using hge1)
    have h2 : (2 : ℝ) ^ (kwin 2 L 1) ≤ 2 * lam L 2 := two_pow_kwin_le L 1 (by simpa using hge2)
    have hmink := hA L hrk
    calc (2 : ℝ) ^ (kwin 2 L 0 + kwin 2 L 1)
        = (2 : ℝ) ^ (kwin 2 L 0) * (2 : ℝ) ^ (kwin 2 L 1) := pow_add _ _ _
      _ ≤ (2 * lam L 1) * (2 * lam L 2) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 4 * (lam L 1 * lam L 2) := by ring
      _ ≤ 8 * detL L := by linarith
      _ ≤ 8 * (Δ + 1) := by linarith
  -- Step 3: assemble.
  have hsum2 : (∑ L ∈ F, (ballCount L X : ℝ))
      = ∑ k ∈ Kx, ∑ L ∈ F.filter (fun L => kf L = k), (ballCount L X : ℝ) := by
    rw [Finset.sum_fiberwise_of_maps_to (s := F) (t := Kx) (g := kf)
      (fun L hL => hkf_mem L hL) (fun L => (ballCount L X : ℝ))]
  have hsum3 : (∑ k ∈ Kx, ∑ L ∈ F.filter (fun L => kf L = k), (ballCount L X : ℝ))
      ≤ ∑ k ∈ Kx, 4 * KB * KC * X ^ 2 * (2 : ℝ) ^ (n * (k.1 + k.2)) :=
    Finset.sum_le_sum hclass
  have hsum4 : (∑ k ∈ Kx, 4 * KB * KC * X ^ 2 * (2 : ℝ) ^ (n * (k.1 + k.2)))
      = 4 * KB * KC * X ^ 2 * ∑ k ∈ Kx, (2 : ℝ) ^ (n * (k.1 + k.2)) := by
    rw [Finset.mul_sum]
  have hfin : (∑ k ∈ Kx, (2 : ℝ) ^ (n * (k.1 + k.2))) ≤ KD * Δ ^ n * Real.log (2 * Δ) :=
    hDy Δ Kx hΔ hcons
  have hX2 : 0 ≤ 4 * KB * KC * X ^ 2 := by positivity
  calc ((S.ncard : ℕ) : ℝ) ≤ ∑ L ∈ F, (ballCount L X : ℝ) := hstep1
    _ = ∑ k ∈ Kx, ∑ L ∈ F.filter (fun L => kf L = k), (ballCount L X : ℝ) := hsum2
    _ ≤ ∑ k ∈ Kx, 4 * KB * KC * X ^ 2 * (2 : ℝ) ^ (n * (k.1 + k.2)) := hsum3
    _ = 4 * KB * KC * X ^ 2 * ∑ k ∈ Kx, (2 : ℝ) ^ (n * (k.1 + k.2)) := hsum4
    _ ≤ 4 * KB * KC * X ^ 2 * (KD * Δ ^ n * Real.log (2 * Δ)) :=
        mul_le_mul_of_nonneg_left hfin hX2
    _ = 4 * KB * KC * KD * X ^ 2 * Δ ^ n * Real.log (2 * Δ) := by ring

/-- **The number of primitive rank-two lattices with bounded successive minima:**
`#{L : λ_j(L) ≤ s j} ≪ s₀^{n+2} s₁^n`.

Each such `L` is mapped to the pair `(u, w)`, where `u` is a shortest vector of `L` and `w` a
reduced basis partner (`reduced_partner`); the map is injective because `span{u,w} = L`.  The image
lies in a box in the first coordinate (`‖u‖ = λ₁ ≤ s₀`) and, for fixed `u`, in the slab
`|⟨u,w⟩| ≤ ‖u‖²/2` with `‖w‖ ≤ 2λ₂ ≤ 2s₁` (obtained from `detL L ≤ λ₁λ₂`).  Counting with
`slab_ball_ncard` and `box_card` gives the result. -/
theorem num_lattices_two_self (n : ℕ) (hn : 2 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : Fin 2 → ℝ) (F : Finset (Submodule ℤ (Fin (n + 1) → ℤ))),
      (∀ j, 1 ≤ s j) →
      (∀ L ∈ F, IsPrimLat L ∧ rk L = 2 ∧ ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j) →
      (F.card : ℝ) ≤ K * s 0 ^ (n + 2) * s 1 ^ n := by
  classical
  refine ⟨(Real.sqrt ((n : ℝ) + 1) + 1) * 7 ^ n * 5 ^ (n + 1), by positivity, ?_⟩
  intro s F hs hF
  set A : ℝ := s 0 with hAs
  set B : ℝ := s 1 with hBs
  have hA1 : 1 ≤ A := by rw [hAs]; exact hs 0
  have hB1 : 1 ≤ B := by rw [hBs]; exact hs 1
  -- shortest vectors
  have hexu : ∀ L ∈ F, ∃ u : Fin (n + 1) → ℤ, u ∈ L ∧ u ≠ 0 ∧ eNorm u = lam L 1 ∧
      (∀ z : Fin (n + 1) → ℤ, z ∈ L → z ≠ 0 → eNorm u ≤ eNorm z) := by
    intro L hL
    obtain ⟨-, hrk, -⟩ := hF L hL
    obtain ⟨u, huL, hu0, hueq⟩ := exists_shortest_vec L (by omega : 1 ≤ rk L)
    exact ⟨u, huL, hu0, hueq, fun z hz hz0 => by rw [hueq]; exact lam_one_le_eNorm L hz hz0⟩
  let uf : Submodule ℤ (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℤ) := fun L =>
    if h : L ∈ F then Classical.choose (hexu L h) else 0
  have huf : ∀ L ∈ F, uf L ∈ L ∧ uf L ≠ 0 ∧ eNorm (uf L) = lam L 1 ∧
      (∀ z : Fin (n + 1) → ℤ, z ∈ L → z ≠ 0 → eNorm (uf L) ≤ eNorm z) := by
    intro L hL
    simp only [uf, dif_pos hL]
    exact Classical.choose_spec (hexu L hL)
  -- reduced basis partners
  let wf : Submodule ℤ (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℤ) := fun L =>
    if h : L ∈ F then
      Classical.choose (reduced_partner L (hF L h).2.1 (uf L) (huf L h).1 (huf L h).2.1
        (huf L h).2.2.2)
    else 0
  have hwf : ∀ L ∈ F, wf L ∈ L ∧ Submodule.span ℤ (Set.range ![uf L, wf L]) = L ∧
      |((dotZ (wf L) (uf L) : ℤ) : ℝ)| ≤ ((dotZ (uf L) (uf L) : ℤ) : ℝ) / 2 := by
    intro L hL
    simp only [wf, dif_pos hL]
    exact Classical.choose_spec (reduced_partner L (hF L hL).2.1 (uf L) (huf L hL).1
      (huf L hL).2.1 (huf L hL).2.2.2)
  -- the injection
  set φ : Submodule ℤ (Fin (n + 1) → ℤ) → ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
    fun L => (uf L, wf L) with hφ
  have hinj : Set.InjOn φ (F : Set (Submodule ℤ (Fin (n + 1) → ℤ))) := by
    intro L hL L' hL' hEq
    have h1 : uf L = uf L' := congrArg Prod.fst hEq
    have h2 : wf L = wf L' := congrArg Prod.snd hEq
    rw [← (hwf L hL).2.1, ← (hwf L' hL').2.1, h1, h2]
  set G : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) := F.image φ with hG
  have hGcard : (F.card : ℝ) = (G.card : ℝ) := by
    rw [hG, Finset.card_image_of_injOn hinj]
  set U : Finset (Fin (n + 1) → ℤ) := G.image Prod.fst with hU
  have hGsum : (G.card : ℝ) = ∑ u ∈ U, (((G.filter (fun p => p.1 = u)).card : ℕ) : ℝ) := by
    rw [hU, Finset.card_eq_sum_card_image (f := Prod.fst) (s := G)]
    push_cast
    rfl
  -- the fibre bound
  have hfiber : ∀ u ∈ U, (((G.filter (fun p => p.1 = u)).card : ℕ) : ℝ) ≤
      (Real.sqrt (n + 1) + 1) * eNorm u * (7 * B) ^ n := by
    intro u hu
    obtain ⟨L, hL, huL⟩ : ∃ L ∈ F, uf L = u := by
      rw [hU] at hu
      obtain ⟨p, hpG, hpu⟩ := Finset.mem_image.mp hu
      rw [hG] at hpG
      obtain ⟨L, hLF, hLG⟩ := Finset.mem_image.mp hpG
      refine ⟨L, hLF, ?_⟩
      show Prod.fst (φ L) = u
      rw [hLG, hpu]
    have hu0 : u ≠ 0 := by rw [← huL]; exact (huf L hL).2.1
    have hfin : ({v : Fin (n + 1) → ℤ | |((dotZ u v : ℤ) : ℝ)| ≤ eNorm u ^ 2 / 2 ∧
        eNorm v ≤ 2 * B} : Set (Fin (n + 1) → ℤ)).Finite :=
      (MDBasic.finite_eNorm_le (2 * B)).subset (fun v hv => hv.2)
    have hmaps : ∀ p ∈ G.filter (fun p => p.1 = u),
        p.2 ∈ ({v : Fin (n + 1) → ℤ | |((dotZ u v : ℤ) : ℝ)| ≤ eNorm u ^ 2 / 2 ∧
          eNorm v ≤ 2 * B} : Set (Fin (n + 1) → ℤ)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpG, hp1⟩ := hp
      rw [hG] at hpG
      obtain ⟨L', hL'F, hL'G⟩ := Finset.mem_image.mp hpG
      have huf' : uf L' = u := by
        show Prod.fst (φ L') = u
        rw [hL'G, hp1]
      have hw' : p.2 = wf L' := by
        show p.2 = Prod.snd (φ L')
        rw [← hL'G]
      rw [hw']
      refine ⟨?_, ?_⟩
      · have hred := (hwf L' hL'F).2.2
        rw [dotZ_comm u (wf L'), eNorm_sq_eq]
        rwa [huf'] at hred
      · -- the norm of the partner
        have hli : LinearIndependent ℤ ![u, wf L'] := by
          rw [linearIndependent_iff_card_le_finrank_span]
          have hfin2 : Set.finrank ℤ (Set.range ![u, wf L']) = rk L' := by
            change Module.finrank ℤ ↥(Submodule.span ℤ (Set.range ![u, wf L'])) = rk L'
            rw [← huf', (hwf L' hL'F).2.1, rk]
          rw [hfin2, (hF L' hL'F).2.1]
          simp
        have hdet2 : detL L' ^ 2 = eNorm u ^ 2 * eNorm (wf L') ^ 2
            - ((dotZ (wf L') u : ℤ) : ℝ) ^ 2 := by
          have hset : ({u, wf L'} : Set (Fin (n + 1) → ℤ)) = Set.range ![u, wf L'] := by
            ext z; simp [or_comm]
          have h := ESL.detL_span_pair_sq u (wf L') hli
          rw [hset, dotZ_comm u (wf L')] at h
          have hspan'' : Submodule.span ℤ (Set.range ![u, wf L']) = L' := by
            rw [← huf', (hwf L' hL'F).2.1]
          rwa [hspan''] at h
        have hred := (hwf L' hL'F).2.2
        rw [huf'] at hred
        have hb : ((dotZ (wf L') u : ℤ) : ℝ) ^ 2 ≤ (eNorm u ^ 2 / 2) ^ 2 := by
          have h1 : |((dotZ (wf L') u : ℤ) : ℝ)| ≤ eNorm u ^ 2 / 2 := by
            rw [eNorm_sq_eq]
            exact hred
          have h2 : |eNorm u ^ 2 / 2| = eNorm u ^ 2 / 2 :=
            abs_of_nonneg (by positivity)
          have h1' : |((dotZ (wf L') u : ℤ) : ℝ)| ≤ |eNorm u ^ 2 / 2| := by
            rw [h2]
            exact h1
          exact sq_le_sq.mpr h1'
        have hU2 : eNorm u ^ 2 ≤ B ^ 2 := by
          have h1 : eNorm u ≤ B := by
            have hrk' : rk L' = 2 := (hF L' hL'F).2.1
            have h12 : lam L' 1 ≤ lam L' 2 := lam_mono L' (by norm_num) (by omega)
            have h2 : lam L' 2 ≤ B := by rw [hBs]; exact (hF L' hL'F).2.2 1
            rw [← huf', (huf L' hL'F).2.2.1]
            exact le_trans h12 h2
          nlinarith [h1, eNorm_nonneg u, hB1]
        have hml := FM.minkowski_lower L'
        rw [(hF L' hL'F).2.1] at hml
        have hprod : (∏ i ∈ Finset.range 2, lam L' (i + 1)) = lam L' 1 * lam L' 2 := by
          rw [Finset.prod_range_succ, Finset.prod_range_one]
        rw [hprod] at hml
        have hd : detL L' ≤ eNorm u * B := by
          have h1 : lam L' 1 = eNorm u := by
            rw [← huf', (huf L' hL'F).2.2.1]
          have h2 : lam L' 2 ≤ B := by rw [hBs]; exact (hF L' hL'F).2.2 1
          rw [h1] at hml
          exact hml.trans (mul_le_mul_of_nonneg_left h2 (eNorm_nonneg u))
        have hUpos : 0 < eNorm u ^ 2 := by
          have := eNorm_pos_of_ne_zero hu0
          positivity
        have hU4 : eNorm u ^ 4 ≤ eNorm u ^ 2 * B ^ 2 := by
          nlinarith [hU2, sq_nonneg (eNorm u)]
        have hd2 : detL L' ^ 2 ≤ (eNorm u * B) ^ 2 := pow_le_pow_left₀ (detL_nonneg L') hd 2
        have h6 : eNorm (wf L') ^ 2 ≤ 4 * B ^ 2 := by
          have hkey : eNorm u ^ 2 * eNorm (wf L') ^ 2 ≤ eNorm u ^ 2 * B ^ 2 + eNorm u ^ 4 / 4 := by
            nlinarith [hdet2, hb, hd2]
          have hstep : eNorm u ^ 2 * eNorm (wf L') ^ 2 ≤ eNorm u ^ 2 * (4 * B ^ 2) := by
            nlinarith [hkey, hU4]
          have h7 : eNorm u ^ 2 * (4 * B ^ 2) / eNorm u ^ 2 = 4 * B ^ 2 :=
            mul_div_cancel_left₀ _ (ne_of_gt hUpos)
          have h8 : eNorm (wf L') ^ 2 ≤ eNorm u ^ 2 * (4 * B ^ 2) / eNorm u ^ 2 := by
            rw [le_div_iff₀ hUpos]
            linarith [hstep]
          rwa [h7] at h8
        nlinarith [h6, eNorm_nonneg (wf L'), hB1]
    -- count the fibres
    set Fib : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) := G.filter (fun p => p.1 = u) with hFib
    have hinj2 : Set.InjOn Prod.snd (Fib : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))) := by
      intro p hp q hq heq
      rw [Finset.mem_coe, Finset.mem_filter] at hp hq
      exact Prod.ext (by rw [hp.2, hq.2]) heq
    have hcard2 : (((Fib.image Prod.snd).card : ℕ) : ℝ) ≤
        (({v : Fin (n + 1) → ℤ | |((dotZ u v : ℤ) : ℝ)| ≤ eNorm u ^ 2 / 2 ∧
          eNorm v ≤ 2 * B} : Set (Fin (n + 1) → ℤ)).ncard : ℝ) := by
      have hsub : ((Fib.image Prod.snd : Finset (Fin (n + 1) → ℤ)) : Set (Fin (n + 1) → ℤ)) ⊆
          ({v : Fin (n + 1) → ℤ | |((dotZ u v : ℤ) : ℝ)| ≤ eNorm u ^ 2 / 2 ∧
            eNorm v ≤ 2 * B} : Set (Fin (n + 1) → ℤ)) := by
        intro v hv
        rw [Finset.mem_coe] at hv
        rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
        exact hmaps p hp
      have h := Set.ncard_le_ncard hsub hfin
      rw [Set.ncard_coe_finset] at h
      exact_mod_cast h
    have hcard1 : (((G.filter (fun p => p.1 = u)).card : ℕ) : ℝ)
        = (((Fib.image Prod.snd).card : ℕ) : ℝ) := by
      rw [hFib]
      rw [Finset.card_image_of_injOn hinj2]
    rw [hcard1]
    calc (((Fib.image Prod.snd).card : ℕ) : ℝ)
        ≤ (({v : Fin (n + 1) → ℤ | |((dotZ u v : ℤ) : ℝ)| ≤ eNorm u ^ 2 / 2 ∧
            eNorm v ≤ 2 * B} : Set (Fin (n + 1) → ℤ)).ncard : ℝ) := hcard2
      _ ≤ (Real.sqrt ((n : ℝ) + 1) + 1) * eNorm u * (2 * ((⌈2 * B⌉₊ : ℕ) : ℝ) + 1) ^ (n + 1 - 1) := by
          have h := ESL.slab_ball_ncard u hu0 (2 * B)
          simpa using h
      _ ≤ (Real.sqrt ((n : ℝ) + 1) + 1) * eNorm u * (7 * B) ^ n := by
          have hceil : ((⌈2 * B⌉₊ : ℕ) : ℝ) < 2 * B + 1 := Nat.ceil_lt_add_one (by linarith)
          have h7 : 2 * ((⌈2 * B⌉₊ : ℕ) : ℝ) + 1 ≤ 7 * B := by linarith
          have hexp : n + 1 - 1 = n := by omega
          rw [hexp]
          have hb1 : (0 : ℝ) ≤ 2 * ((⌈2 * B⌉₊ : ℕ) : ℝ) + 1 := by linarith
          have hpow : (2 * ((⌈2 * B⌉₊ : ℕ) : ℝ) + 1) ^ n ≤ (7 * B) ^ n :=
            pow_le_pow_left₀ hb1 h7 n
          have hnn : (0 : ℝ) ≤ (Real.sqrt ((n : ℝ) + 1) + 1) * eNorm u :=
            mul_nonneg (by positivity) (eNorm_nonneg u)
          exact mul_le_mul_of_nonneg_left hpow hnn
  -- the box of first coordinates
  have hue_le : ∀ u ∈ U, eNorm u ≤ A := by
    intro u hu
    rw [hU] at hu
    obtain ⟨p, hpG, hpu⟩ := Finset.mem_image.mp hu
    rw [hG] at hpG
    obtain ⟨L, hLF, hLG⟩ := Finset.mem_image.mp hpG
    have hufL : uf L = u := by
      show Prod.fst (φ L) = u
      rw [hLG, hpu]
    rw [← hufL, (huf L hLF).2.2.1, hAs]
    exact (hF L hLF).2.2 0
  have hUbound : ((U.card : ℕ) : ℝ) ≤ 5 ^ (n + 1) * A ^ (n + 1) := by
    have hsub : (U : Set (Fin (n + 1) → ℤ)) ⊆
        ((Fintype.piFinset (fun _ : Fin (n + 1) =>
          Finset.Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊)) : Finset (Fin (n + 1) → ℤ)) : Set _) := by
      intro u hu
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro i
      obtain ⟨h1, h2⟩ := abs_le.mp (le_trans (ESL.eNorm_coord_le u i) (hue_le u hu))
      have hAc : A ≤ ((⌈A⌉₊ : ℕ) : ℝ) := Nat.le_ceil A
      refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · have h3 : ((-(⌈A⌉₊ : ℤ) : ℤ) : ℝ) ≤ ((u i : ℤ) : ℝ) := by
          push_cast
          linarith
        exact_mod_cast h3
      · have h3 : ((u i : ℤ) : ℝ) ≤ ((⌈A⌉₊ : ℤ) : ℝ) := by
          push_cast
          linarith
        exact_mod_cast h3
    have h1 : ((U.card : ℕ) : ℝ) ≤
        ((Fintype.piFinset (fun _ : Fin (n + 1) =>
          Finset.Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊)) : Finset (Fin (n + 1) → ℤ)).card : ℝ) := by
      have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset] at h
      exact_mod_cast h
    have h2 : ((Fintype.piFinset (fun _ : Fin (n + 1) =>
          Finset.Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊)) : Finset (Fin (n + 1) → ℤ)).card : ℝ)
        = (2 * ((⌈A⌉₊ : ℕ) : ℝ) + 1) ^ (n + 1) := by
      have h := (box_card (ι := Fin (n + 1)) ⌈A⌉₊).1
      simpa using h
    rw [h2] at h1
    have hceil : ((⌈A⌉₊ : ℕ) : ℝ) < A + 1 := Nat.ceil_lt_add_one (by linarith)
    have h5 : 2 * ((⌈A⌉₊ : ℕ) : ℝ) + 1 ≤ 5 * A := by linarith
    have hb1 : (0 : ℝ) ≤ 2 * ((⌈A⌉₊ : ℕ) : ℝ) + 1 := by linarith
    have hpow : (2 * ((⌈A⌉₊ : ℕ) : ℝ) + 1) ^ (n + 1) ≤ (5 * A) ^ (n + 1) :=
      pow_le_pow_left₀ hb1 h5 (n + 1)
    have h3 : (5 * A) ^ (n + 1) = 5 ^ (n + 1) * A ^ (n + 1) := by rw [mul_pow]
    linarith [h1, hpow, h3]
  -- assembly
  have hsum : (G.card : ℝ) ≤ ∑ u ∈ U, (Real.sqrt ((n : ℝ) + 1) + 1) * A * (7 * B) ^ n := by
    rw [hGsum]
    refine Finset.sum_le_sum (fun u hu => ?_)
    have h1 : (Real.sqrt ((n : ℝ) + 1) + 1) * eNorm u ≤ (Real.sqrt ((n : ℝ) + 1) + 1) * A :=
      mul_le_mul_of_nonneg_left (hue_le u hu) (by positivity)
    have h2 : (Real.sqrt ((n : ℝ) + 1) + 1) * eNorm u * (7 * B) ^ n
        ≤ (Real.sqrt ((n : ℝ) + 1) + 1) * A * (7 * B) ^ n :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    exact le_trans (hfiber u hu) h2
  have hc : (0 : ℝ) ≤ (Real.sqrt ((n : ℝ) + 1) + 1) * A * (7 * B) ^ n := by positivity
  calc (F.card : ℝ) = (G.card : ℝ) := hGcard
    _ ≤ ∑ u ∈ U, (Real.sqrt ((n : ℝ) + 1) + 1) * A * (7 * B) ^ n := hsum
    _ = ((U.card : ℕ) : ℝ) * ((Real.sqrt ((n : ℝ) + 1) + 1) * A * (7 * B) ^ n) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (5 ^ (n + 1) * A ^ (n + 1)) * ((Real.sqrt ((n : ℝ) + 1) + 1) * A * (7 * B) ^ n) :=
        mul_le_mul_of_nonneg_right hUbound hc
    _ = ((Real.sqrt ((n : ℝ) + 1) + 1) * 7 ^ n * 5 ^ (n + 1)) * A ^ (n + 2) * B ^ n := by
        rw [mul_pow]; ring
    _ = ((Real.sqrt ((n : ℝ) + 1) + 1) * 7 ^ n * 5 ^ (n + 1)) * s 0 ^ (n + 2) * s 1 ^ n := by
        rw [hAs, hBs]

/-- The paper's `ℓ_{2,n}(X;Δ)` count: `#{x ≠ 0 : ‖x‖ ≤ X, 𝔡₂(x) ≤ Δ} ≪ X² Δⁿ log(2Δ)`. -/
theorem ell_two_count_free (n : ℕ) (hn : 2 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ X Δ : ℝ, 1 ≤ X → 1 ≤ Δ →
      (({x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ X ∧ dmin 2 {x} ≤ Δ}).ncard : ℝ)
        ≤ K * X ^ 2 * Δ ^ n * Real.log (2 * Δ) := by
  obtain ⟨KC, hKCpos, hC⟩ := num_lattices_two_self n hn
  obtain ⟨KB, hKBpos, hB⟩ := ballCount_two_le (ι := Fin (n + 1))
  obtain ⟨KD, hKDpos, hDy⟩ := dyadic_sum_bound n hn
  have hcard2 : 2 ≤ Fintype.card (Fin (n + 1)) := by
    rw [Fintype.card_fin]
    omega
  exact ell_two_count_aux n hn
    (fun x D hx hD => dmin_two_singleton_le hcard2 x hx D hD)
    KC hKCpos hC
    (fun L hrk => lam_two_mul_le_detL_self L hrk)
    KB hKBpos hB KD hKDpos hDy

end Work.HP.FM3
