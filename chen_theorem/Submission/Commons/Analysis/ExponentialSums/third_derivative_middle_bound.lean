import Mathlib
import Submission.Commons.Analysis.ExponentialSums.vdc_second_moment
import Submission.Commons.Analysis.ExponentialSums.correlation_shift_bound
import Submission.Commons.Analysis.Asymptotics.sum_range_neg_half_le

open Complex Filter
open scoped ComplexConjugate Real BigOperators Topology Filter
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Commons.Analysis.ExponentialSums

noncomputable section

namespace mid

/-- `e(x) := exp(2πi·x)` -/
def eR (x : ℝ) : ℂ := Complex.exp ((((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))

/-- Phase conjugation identity `conj(e(r)) = e(-r)`. -/
lemma eR_conj (r : ℝ) : conj (eR r) = eR (-r) := by
  dsimp [eR]
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  apply Complex.ext <;> simp <;> ring

/-- `e(x+y) = e(x)·e(y)`. -/
lemma eR_add (x y : ℝ) : eR (x + y) = eR x * eR y := by
  dsimp [eR]
  rw [← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp <;> ring

/-- `e(r)·conj(e(r)) = 1`. -/
lemma eR_self_conj (r : ℝ) : eR r * conj (eR r) = 1 := by
  have hnorm : ‖eR r‖ = 1 := by
    dsimp [eR]
    exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * r)
  rw [Complex.mul_conj', hnorm]
  norm_num

/-- The phase `e(f(n))`, cut to the block `Icc (a+1) (a+M)`. -/
def uPhase (a : ℤ) (M : ℕ) (f : ℝ → ℝ) : ℤ → ℂ :=
  fun n => if n ∈ Finset.Icc (a + 1) (a + (M : ℤ)) then eR (f (n : ℝ)) else 0

/-- Support of the phase block. -/
lemma uPhase_support {a : ℤ} {M : ℕ} (f : ℝ → ℝ) :
    ∀ n : ℤ, uPhase a M f n ≠ 0 → n ∈ Finset.Icc (a + 1) (a + (M : ℤ)) := by
  intro n hn
  by_contra h
  simp [uPhase, h] at hn

/-- Value of the phase block inside the block. -/
lemma uPhase_val {a : ℤ} {M : ℕ} (f : ℝ → ℝ) {n : ℤ}
    (hn : n ∈ Finset.Icc (a + 1) (a + (M : ℤ))) :
    uPhase a M f n = eR (f (n : ℝ)) := by
  simp [uPhase, hn]

/-- Sum of the phase block over the block equals the plain phase sum. -/
lemma uPhase_sum_eq {a : ℤ} {M : ℕ} (f : ℝ → ℝ) :
    (∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)), uPhase a M f n) =
      ∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)), eR (f (n : ℝ)) := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  exact uPhase_val f hn

/-- the symmetric window `|t| ≤ Q-1` -/
def win (Q : ℕ) : Finset ℤ :=
  Finset.Icc (-(((Q - 1 : ℕ) : ℤ))) (((Q - 1 : ℕ) : ℤ))

/-- the positive window `1 ≤ s ≤ Q-1` as a ℤ interval -/
def posWinZ (Q : ℕ) : Finset ℤ := Finset.Icc (1 : ℤ) (((Q - 1 : ℕ) : ℤ))

/-- the negative window `-(Q-1) ≤ s ≤ -1` as a ℤ interval -/
def negWinZ (Q : ℕ) : Finset ℤ := Finset.Icc (-(((Q - 1 : ℕ) : ℤ))) (-(1 : ℤ))

/-- the positive window as a ℕ interval -/
def posWinN (Q : ℕ) : Finset ℕ := Finset.Icc 1 (Q - 1)

/-- decomposition of the window into `{0}`, positive and negative parts -/
lemma win_split (g : ℤ → ℝ) {Q : ℕ} :
    (∑ t ∈ win Q, g t) = g 0 + (∑ t ∈ posWinZ Q, g t) + (∑ t ∈ negWinZ Q, g t) := by
  classical
  let K : ℤ := ((Q - 1 : ℕ) : ℤ)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact_mod_cast (Nat.zero_le (Q - 1))
  have hpart : win Q = ({0} : Finset ℤ) ∪ posWinZ Q ∪ negWinZ Q := by
    ext t
    simp [win, posWinZ, negWinZ, K, Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj1 : Disjoint (({0} : Finset ℤ) ∪ posWinZ Q) (negWinZ Q) := by
    rw [Finset.disjoint_left]
    intro x hx hxB
    simp [posWinZ, negWinZ, K, Finset.mem_union, Finset.mem_Icc] at hx hxB
    rcases hx with hx | hx
    · omega
    · omega
  have hdisj2 : Disjoint ({0} : Finset ℤ) (posWinZ Q) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp [posWinZ, Finset.mem_Icc] at hxA hxB
    omega
  have hz : (∑ t ∈ ({0} : Finset ℤ), g t) = g 0 := by simp
  calc
    (∑ t ∈ win Q, g t) = ∑ t ∈ ({0} : Finset ℤ) ∪ posWinZ Q ∪ negWinZ Q, g t := by rw [hpart]
    _ = ((∑ t ∈ ({0} : Finset ℤ) ∪ posWinZ Q, g t) + ∑ t ∈ negWinZ Q, g t) := by
          rw [Finset.sum_union hdisj1]
    _ = ((∑ t ∈ ({0} : Finset ℤ), g t) + ∑ t ∈ posWinZ Q, g t) +
          ∑ t ∈ negWinZ Q, g t := by
          rw [Finset.sum_union hdisj2]
    _ = g 0 + (∑ t ∈ posWinZ Q, g t) + (∑ t ∈ negWinZ Q, g t) := by rw [hz]

/-- the negative window sum equals the positive window sum with `-t` -/
lemma neg_sum_eq_pos (g : ℤ → ℝ) {Q : ℕ} :
    (∑ t ∈ negWinZ Q, g t) = ∑ u ∈ posWinZ Q, g (-u) := by
  classical
  refine Finset.sum_bij (s := negWinZ Q) (t := posWinZ Q) (f := g)
    (g := fun u => g (-u)) (i := fun t _ht => -t) ?hi ?hinj ?hsurj ?hval
  · intro t ht
    simp [negWinZ, posWinZ, Finset.mem_Icc] at ht ⊢
    omega
  · intro t1 ht1 t2 ht2 h
    omega
  · intro u hu
    refine ⟨-u, ?_, ?_⟩
    · simp [negWinZ, posWinZ, Finset.mem_Icc] at hu ⊢
      omega
    · simp
  · intro t ht
    simp

/-- positive ℤ window sum equals the ℕ-indexed sum -/
lemma pos_sum_nat (g : ℤ → ℝ) {Q : ℕ} :
    (∑ t ∈ posWinZ Q, g t) = ∑ s ∈ posWinN Q, g (s : ℤ) := by
  classical
  refine Finset.sum_bij (s := posWinZ Q) (t := posWinN Q) (f := g)
    (g := fun s => g (s : ℤ)) (i := fun t _ht => t.toNat) ?hi ?hinj ?hsurj ?hval
  · intro t ht
    simp [posWinZ, Finset.mem_Icc] at ht
    have htn : 0 ≤ t := by omega
    have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htn
    change t.toNat ∈ Finset.Icc 1 (Q - 1)
    rw [Finset.mem_Icc]
    constructor
    · have h1 : (1 : ℤ) ≤ t.toNat := by rw [← htcast]; omega
      exact_mod_cast h1
    · have h2 : (t.toNat : ℤ) ≤ ((Q - 1 : ℕ) : ℤ) := by rw [← htcast]; omega
      exact_mod_cast h2
  · intro t1 ht1 t2 ht2 h
    have ht1n : 0 ≤ t1 := by
      simp [posWinZ, Finset.mem_Icc] at ht1
      omega
    have ht2n : 0 ≤ t2 := by
      simp [posWinZ, Finset.mem_Icc] at ht2
      omega
    have h1 : (t1.toNat : ℤ) = t1 := Int.toNat_of_nonneg ht1n
    have h2 : (t2.toNat : ℤ) = t2 := Int.toNat_of_nonneg ht2n
    omega
  · intro s hs
    change s ∈ Finset.Icc 1 (Q - 1) at hs
    rw [Finset.mem_Icc] at hs
    refine ⟨(s : ℤ), ?_, ?_⟩
    · change (s : ℤ) ∈ Finset.Icc (1 : ℤ) (((Q - 1 : ℕ) : ℤ))
      rw [Finset.mem_Icc]
      constructor <;> omega
    · simp
  · intro t ht
    have htn : 0 ≤ t := by
      simp [posWinZ, Finset.mem_Icc] at ht
      omega
    rw [Int.toNat_of_nonneg htn]

/-- window sum of an even function: `Σ_{|t|≤Q-1} c(t) = c 0 + 2·Σ_{1≤s≤Q-1} c(s)` -/
lemma win_sum_even {Q : ℕ} (c : ℤ → ℝ) (hc : ∀ t : ℤ, c (-t) = c t) :
    (∑ t ∈ win Q, c t) = c 0 + 2 * (∑ s ∈ posWinN Q, c (s : ℤ)) := by
  rw [win_split c]
  have hneg : (∑ t ∈ negWinZ Q, c t) = ∑ u ∈ posWinZ Q, c u := by
    calc
      (∑ t ∈ negWinZ Q, c t) = ∑ u ∈ posWinZ Q, c (-u) := neg_sum_eq_pos c
      _ = ∑ u ∈ posWinZ Q, c u := by
            apply Finset.sum_congr rfl
            intro u hu
            exact hc u
  calc
    c 0 + (∑ t ∈ posWinZ Q, c t) + (∑ t ∈ negWinZ Q, c t)
        = c 0 + (∑ t ∈ posWinZ Q, c t) + (∑ u ∈ posWinZ Q, c u) := by rw [hneg]
    _ = c 0 + 2 * (∑ s ∈ posWinN Q, c (s : ℤ)) := by
          rw [pos_sum_nat (g := c)]
          ring

/-- correlation sum for the phase block -/
def corrSum (a : ℤ) (M : ℕ) (f : ℝ → ℝ) (t : ℤ) : ℂ :=
  ∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)), uPhase a M f (n + t) * conj (uPhase a M f n)

/-- correlation norm -/
def corrNorm (a : ℤ) (M : ℕ) (f : ℝ → ℝ) (t : ℤ) : ℝ := ‖corrSum a M f t‖

/-- number of elements of the block -/
lemma block_card (a : ℤ) (M : ℕ) : (Finset.Icc (a + 1) (a + (M : ℤ))).card = M := by
  rw [Int.card_Icc]
  have hcalc : ((a + (M : ℤ)) + 1 - (a + 1)) = (M : ℤ) := by ring
  rw [hcalc]
  exact Int.toNat_natCast M

/-- zero shift correlation: `corrSum 0 = M` -/
lemma corrSum_zero (a : ℤ) (M : ℕ) (f : ℝ → ℝ) : corrSum a M f 0 = (M : ℂ) := by
  classical
  unfold corrSum
  calc
    (∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)), uPhase a M f (n + 0) * conj (uPhase a M f n))
        = ∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)), uPhase a M f n * conj (uPhase a M f n) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simp
    _ = ∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)), (1 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [uPhase_val f hn]
            exact eR_self_conj (f (n : ℝ))
    _ = (M : ℂ) := by
            rw [Finset.sum_const]
            simp [block_card]

/-- norm of the diagonal correlation -/
lemma corrNorm_zero (a : ℤ) (M : ℕ) (f : ℝ → ℝ) : corrNorm a M f 0 = (M : ℝ) := by
  unfold corrNorm
  rw [corrSum_zero]
  have hM : 0 ≤ (M : ℝ) := by exact_mod_cast (Nat.zero_le M)
  rw [← Complex.ofReal_natCast]
  exact (RCLike.norm_ofReal (M : ℝ)).trans (abs_of_nonneg hM)

/-- filtered (pair) form of the correlation sum -/
def corrSumF (a : ℤ) (M : ℕ) (f : ℝ → ℝ) (t : ℤ) : ℂ :=
  ∑ n ∈ (Finset.Icc (a + 1) (a + (M : ℤ))).filter (fun n => n + t ∈ Finset.Icc (a + 1) (a + (M : ℤ))),
    uPhase a M f (n + t) * conj (uPhase a M f n)

/-- correlation sum equals its filtered form -/
lemma corrSum_eq_corrSumF {a : ℤ} {M : ℕ} (f : ℝ → ℝ) (t : ℤ) :
    corrSum a M f t = corrSumF a M f t := by
  classical
  unfold corrSum corrSumF
  let I : Finset ℤ := Finset.Icc (a + 1) (a + (M : ℤ))
  change (∑ n ∈ I, uPhase a M f (n + t) * conj (uPhase a M f n)) =
      ∑ n ∈ I.filter (fun n => n + t ∈ I), uPhase a M f (n + t) * conj (uPhase a M f n)
  exact (Finset.sum_subset (Finset.filter_subset (fun n => n + t ∈ I) I) (by
      intro x hxI hxF
      have hxI' : x + t ∉ I := by
        intro hxt
        exact hxF (by simp [hxI, hxt])
      have hu : uPhase a M f (x + t) = 0 := by
        by_contra h
        exact hxI' (uPhase_support f (x + t) h)
      simp [hu])).symm



/-- negative-shift correlation is the conjugate of the positive one -/
lemma corrSum_neg_conj {a : ℤ} {M : ℕ} (f : ℝ → ℝ) (t : ℤ) :
    corrSum a M f (-t) = conj (corrSum a M f t) := by
  classical
  let I : Finset ℤ := Finset.Icc (a + 1) (a + (M : ℤ))
  let Fneg : Finset ℤ := I.filter (fun n => n - t ∈ I)
  let Fpos : Finset ℤ := I.filter (fun n => n + t ∈ I)
  let P : ℂ := ∑ m ∈ Fpos, uPhase a M f m * conj (uPhase a M f (m + t))
  have hreindex : (∑ n ∈ Fneg, uPhase a M f (n - t) * conj (uPhase a M f n)) = P := by
    dsimp [P]
    refine Finset.sum_bij (s := Fneg) (t := Fpos)
      (f := fun n => uPhase a M f (n - t) * conj (uPhase a M f n))
      (g := fun m => uPhase a M f m * conj (uPhase a M f (m + t)))
      (i := fun n _hn => n - t) ?hi ?hinj ?hsurj ?hval
    · intro n hn
      simp [Fneg, Fpos, Finset.mem_filter] at hn ⊢
      constructor
      · exact hn.2
      · exact hn.1
    · intro n1 hn1 n2 hn2 h
      omega
    · intro m hm
      simp [Fneg, Fpos, Finset.mem_filter] at hm
      refine ⟨m + t, ?_, ?_⟩
      · simp [Fneg, Finset.mem_filter]
        constructor
        · exact hm.2
        · exact hm.1
      · omega
    · intro n hn
      have h1 : (n - t) + t = n := by omega
      simp [h1]
  have hA : corrSum a M f (-t) = ∑ n ∈ Fneg, uPhase a M f (n - t) * conj (uPhase a M f n) := by
    have hset : I.filter (fun n : ℤ => n + (-t) ∈ I) = Fneg := by
      ext n
      simp [I, Fneg, Finset.mem_filter]
      omega
    calc
      corrSum a M f (-t) = ∑ n ∈ I.filter (fun n : ℤ => n + (-t) ∈ I),
          uPhase a M f (n + (-t)) * conj (uPhase a M f n) := by
            exact corrSum_eq_corrSumF f (-t)
      _ = ∑ n ∈ Fneg, uPhase a M f (n - t) * conj (uPhase a M f n) := by
            rw [hset]
            apply Finset.sum_congr rfl
            intro n hn
            have harg : n + (-t) = n - t := by ring
            rw [harg]
  have hpos : conj (corrSum a M f t) = P := by
    rw [corrSum_eq_corrSumF f t]
    unfold corrSumF
    dsimp [P, Fpos]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [map_mul]
    rw [conj_conj]
    ring
  calc
    corrSum a M f (-t) = ∑ n ∈ Fneg, uPhase a M f (n - t) * conj (uPhase a M f n) := hA
    _ = P := hreindex
    _ = conj (corrSum a M f t) := hpos.symm

/-- the shift-s correlation equals the phase-difference sum over the shortened block -/
lemma corrSum_shift_eq {a : ℤ} {M : ℕ} (f : ℝ → ℝ) (s : ℕ) (hsM : s ≤ M) :
    corrSum a M f (s : ℤ) =
      ∑ n ∈ Finset.Icc (a + 1) (a + ((M - s : ℕ) : ℤ)),
        eR (f ((n : ℝ) + (s : ℝ)) - f (n : ℝ)) := by
  classical
  let I : Finset ℤ := Finset.Icc (a + 1) (a + (M : ℤ))
  have hset : I.filter (fun n => n + (s : ℤ) ∈ I) = Finset.Icc (a + 1) (a + ((M - s : ℕ) : ℤ)) := by
    ext n
    simp [I, Finset.mem_filter]
    have hcast : ((M - s : ℕ) : ℤ) = (M : ℤ) - (s : ℤ) := by
      rw [Nat.cast_sub hsM]
    rw [hcast]
    constructor <;> intro h <;> omega
  calc
    corrSum a M f (s : ℤ) = ∑ n ∈ I.filter (fun n => n + (s : ℤ) ∈ I),
        uPhase a M f (n + (s : ℤ)) * conj (uPhase a M f n) := by
          exact corrSum_eq_corrSumF f (s : ℤ)
    _ = ∑ n ∈ Finset.Icc (a + 1) (a + ((M - s : ℕ) : ℤ)),
        uPhase a M f (n + (s : ℤ)) * conj (uPhase a M f n) := by
          rw [hset]
    _ = ∑ n ∈ Finset.Icc (a + 1) (a + ((M - s : ℕ) : ℤ)),
        eR (f ((n : ℝ) + (s : ℝ)) - f (n : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          have hnI : n ∈ I := by
            rw [← hset] at hn
            exact (Finset.mem_filter.mp hn).1
          have hnsI : n + (s : ℤ) ∈ I := by
            rw [← hset] at hn
            exact (Finset.mem_filter.mp hn).2
          rw [uPhase_val f hnsI, uPhase_val f hnI]
          simp
          rw [eR_conj]
          rw [← eR_add]
          ring

/-- correlation norms are even in the shift -/
lemma corrNorm_neg {a : ℤ} {M : ℕ} (f : ℝ → ℝ) (t : ℤ) :
    corrNorm a M f (-t) = corrNorm a M f t := by
  unfold corrNorm
  rw [corrSum_neg_conj]
  exact Complex.norm_conj _


/-- per-shift correlation bound for the phase block, via the second-derivative test -/
lemma corrNorm_shift_le {α : ℝ} (hα : 1 ≤ α) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ {a : ℤ} {M : ℕ} (hM : 1 ≤ M) (f : ℝ → ℝ) {l : ℝ} (hl : 0 < l)
        (hf : ContDiffOn ℝ 3 f (Set.Icc (a : ℝ) ((a : ℝ) + (M : ℝ))))
        (hppp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + (M : ℝ)) →
          l ≤ deriv (deriv (deriv f)) x ∧ deriv (deriv (deriv f)) x ≤ α * l)
        {s : ℕ} (hs1 : 1 ≤ s) (hsM : s < M),
        corrNorm a M f (s : ℤ) ≤
          C₂ * ((((M - s : ℕ) : ℝ) * Real.sqrt ((s : ℝ) * l)) +
              (Real.sqrt ((s : ℝ) * l))⁻¹) := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := correlation_shift_bound (α := α) hα
  refine ⟨C₂, hC₂pos, ?_⟩
  intro a M hM f l hl hf hppp s hs1 hsM
  unfold corrNorm
  have hEq : corrSum a M f (s : ℤ) =
      ∑ n ∈ Finset.Icc (a + 1) (a + ((M - s : ℕ) : ℤ)),
        Complex.exp ((((2 * Real.pi * (f ((n : ℝ) + (s : ℝ)) - f (n : ℝ)) : ℝ) : ℂ) * Complex.I)) := by
    simpa [eR] using corrSum_shift_eq f s (le_of_lt hsM)
  rw [hEq]
  exact hC₂ (a := a) (M := M) hM f (l := l) hl hf hppp s hs1 hsM

/-- `Icc 1 (Q-1) ⊆ range Q` for `1 ≤ Q` -/
lemma posWinN_subset_range (Q : ℕ) (hQ : 1 ≤ Q) :
    posWinN Q ⊆ Finset.range Q := by
  intro s hs
  rw [Finset.mem_range]
  change s ∈ Finset.Icc 1 (Q - 1) at hs
  rw [Finset.mem_Icc] at hs
  omega

/-- crude power sum `Σ_{s∈Icc 1 (Q−1)} √s ≤ Q·√Q` -/
lemma sum_sqrt_posWinN_le (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑ s ∈ posWinN Q, Real.sqrt (s : ℝ)) ≤ (Q : ℝ) * Real.sqrt (Q : ℝ) := by
  have hsub : posWinN Q ⊆ Finset.range Q := posWinN_subset_range Q hQ
  have h1 : (∑ s ∈ posWinN Q, Real.sqrt (s : ℝ)) ≤
      ∑ s ∈ Finset.range Q, Real.sqrt (s : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro s hs hsI
    exact Real.sqrt_nonneg (s : ℝ)
  have h2 : (∑ s ∈ Finset.range Q, Real.sqrt (s : ℝ)) ≤ (Q : ℝ) * Real.sqrt (Q : ℝ) := by
    have hterm : ∀ s ∈ Finset.range Q, Real.sqrt (s : ℝ) ≤ Real.sqrt (Q : ℝ) := by
      intro s hs
      apply Real.sqrt_le_sqrt
      exact_mod_cast (le_of_lt (Finset.mem_range.mp hs))
    have hsum := Finset.sum_le_card_nsmul (Finset.range Q) (fun s => Real.sqrt (s : ℝ))
      (Real.sqrt (Q : ℝ)) hterm
    calc
      (∑ s ∈ Finset.range Q, Real.sqrt (s : ℝ)) ≤ (Finset.range Q).card • Real.sqrt (Q : ℝ) := hsum
      _ = (Q : ℝ) * Real.sqrt (Q : ℝ) := by
            rw [Finset.card_range, nsmul_eq_mul]
  exact le_trans h1 h2

/-- for `0 ≤ x`, `x^(-1/2) = (√x)⁻¹` -/
lemma inv_sqrt_eq_rpow_neg_half {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x)⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg hx]
  rw [← Real.sqrt_eq_rpow x]

/-- crude power sum `Σ_{s∈Icc 1 (Q−1)} 1/√s ≤ 3·√Q` -/
lemma sum_inv_sqrt_posWinN_le (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑ s ∈ posWinN Q, (Real.sqrt (s : ℝ))⁻¹) ≤ 3 * Real.sqrt (Q : ℝ) := by
  have hrewrite : (∑ s ∈ posWinN Q, (Real.sqrt (s : ℝ))⁻¹) =
      ∑ s ∈ posWinN Q, (s : ℝ) ^ (-(1 / 2 : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    exact inv_sqrt_eq_rpow_neg_half (by exact_mod_cast (Nat.zero_le s))
  have hsub : posWinN Q ⊆ Finset.range Q := posWinN_subset_range Q hQ
  calc
    (∑ s ∈ posWinN Q, (Real.sqrt (s : ℝ))⁻¹) =
        ∑ s ∈ posWinN Q, (s : ℝ) ^ (-(1 / 2 : ℝ)) := hrewrite
    _ ≤ ∑ n ∈ Finset.range Q, (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
          intro n hn hnI
          exact Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le n)) (-(1 / 2 : ℝ))
    _ ≤ 3 * Real.sqrt (Q : ℝ) := Commons.Analysis.Asymptotics.sum_range_neg_half_le hQ

/-- `Σ_{s∈Icc 1 (Q−1)} √(s·l) = √l·Σ√s` -/
lemma sum_sqrt_mul_l (Q : ℕ) (l : ℝ) :
    (∑ s ∈ posWinN Q, Real.sqrt ((s : ℝ) * l)) =
      Real.sqrt l * (∑ s ∈ posWinN Q, Real.sqrt (s : ℝ)) := by
  calc
    (∑ s ∈ posWinN Q, Real.sqrt ((s : ℝ) * l)) =
        ∑ s ∈ posWinN Q, Real.sqrt (s : ℝ) * Real.sqrt l := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      rw [Real.sqrt_mul (x := (s : ℝ)) (by exact_mod_cast (Nat.zero_le s)) l]
    _ = ∑ s ∈ posWinN Q, Real.sqrt l * Real.sqrt (s : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      rw [mul_comm]
    _ = Real.sqrt l * (∑ s ∈ posWinN Q, Real.sqrt (s : ℝ)) := by
      rw [Finset.mul_sum]

/-- `Σ_{s∈Icc 1 (Q−1)} (√(s·l))⁻¹ = (√l)⁻¹·Σ(√s)⁻¹` for `0 < l` -/
lemma sum_inv_sqrt_mul_l {Q : ℕ} {l : ℝ} (hl : 0 < l) :
    (∑ s ∈ posWinN Q, (Real.sqrt ((s : ℝ) * l))⁻¹) =
      (Real.sqrt l)⁻¹ * (∑ s ∈ posWinN Q, (Real.sqrt (s : ℝ))⁻¹) := by
  calc
    (∑ s ∈ posWinN Q, (Real.sqrt ((s : ℝ) * l))⁻¹)
        = ∑ s ∈ posWinN Q, (Real.sqrt l)⁻¹ * (Real.sqrt (s : ℝ))⁻¹ := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          have hs1 : 1 ≤ s := by
            change s ∈ Finset.Icc 1 (Q - 1) at hs
            exact (Finset.mem_Icc.mp hs).1
          rw [Real.sqrt_mul (x := (s : ℝ)) (by positivity) l]
          have hs0 : 0 < Real.sqrt (s : ℝ) := by rw [Real.sqrt_pos]; positivity
          have hl0 : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
          field_simp [hs0.ne', hl0.ne']
    _ = (Real.sqrt l)⁻¹ * (∑ s ∈ posWinN Q, (Real.sqrt (s : ℝ))⁻¹) := by
          rw [Finset.mul_sum]


/-- van der Corput square bound with an arbitrary window `Q` (uniform in `Q`) -/
lemma vdc_sq {α : ℝ} (hα : 1 ≤ α) :
    ∃ Csq : ℝ, 0 < Csq ∧
      ∀ {a : ℤ} {M : ℕ} (hM : 1 ≤ M) (f : ℝ → ℝ) {Q : ℕ} (hQ : 1 ≤ Q) (hQM : Q ≤ M)
        {l : ℝ} (hl : 0 < l)
        (hf : ContDiffOn ℝ 3 f (Set.Icc (a : ℝ) ((a : ℝ) + (M : ℝ))))
        (hppp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + (M : ℝ)) →
          l ≤ deriv (deriv (deriv f)) x ∧ deriv (deriv (deriv f)) x ≤ α * l),
        ‖∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)), uPhase a M f n‖ ^ 2 ≤
          ((M : ℝ) + (Q : ℝ)) / (Q : ℝ) *
            ((M : ℝ) + Csq * ((M : ℝ) * Real.sqrt l * (Q : ℝ) * Real.sqrt (Q : ℝ) +
              (Real.sqrt l)⁻¹ * Real.sqrt (Q : ℝ))) := by
  classical
  obtain ⟨C₂, hC₂pos, hC₂⟩ := corrNorm_shift_le (α := α) hα
  let Csq : ℝ := 6 * C₂
  have hCsqpos : 0 < Csq := by
    dsimp [Csq]
    positivity
  refine ⟨Csq, hCsqpos, ?_⟩
  intro a M hM f Q hQ hQM l hl hf hppp
  let m : ℝ := (M : ℝ)
  let A0 : ℝ := Real.sqrt l * (Q : ℝ) * Real.sqrt (Q : ℝ)
  let B0 : ℝ := (Real.sqrt l)⁻¹ * Real.sqrt (Q : ℝ)
  have hC₂_nonneg : 0 ≤ C₂ := le_of_lt hC₂pos
  have hm_nonneg : 0 ≤ m := by positivity
  have hA0_nonneg : 0 ≤ A0 := by
    dsimp [A0]
    positivity
  have hB0_nonneg : 0 ≤ B0 := by
    dsimp [B0]
    positivity
  have hAmB_nonneg : 0 ≤ m * A0 + B0 := add_nonneg (mul_nonneg hm_nonneg hA0_nonneg) hB0_nonneg
  -- vdc second moment, window H := Q
  have hvdc := vdc_second_moment (a := a) (M := M) (H := Q) hM hQ
    (u := uPhase a M f) (by intro n hn; exact uPhase_support f n hn)
  -- the weighted window sum bound
  have hMain0 : (∑ t ∈ win Q, ((Q : ℝ) - ‖(t : ℝ)‖) * corrNorm a M f t) ≤
      (Q : ℝ) * (m + Csq * (m * A0 + B0)) := by
    -- weight ≤ Q
    have hw : (∑ t ∈ win Q, ((Q : ℝ) - ‖(t : ℝ)‖) * corrNorm a M f t) ≤
        (Q : ℝ) * (∑ t ∈ win Q, corrNorm a M f t) := by
      calc
        (∑ t ∈ win Q, ((Q : ℝ) - ‖(t : ℝ)‖) * corrNorm a M f t)
            ≤ ∑ t ∈ win Q, (Q : ℝ) * corrNorm a M f t := by
              apply Finset.sum_le_sum
              intro t ht
              have hwle : (Q : ℝ) - ‖(t : ℝ)‖ ≤ (Q : ℝ) := by
                have hnorm : 0 ≤ ‖(t : ℝ)‖ := norm_nonneg _
                linarith
              exact mul_le_mul_of_nonneg_right hwle (norm_nonneg _)
        _ = (Q : ℝ) * (∑ t ∈ win Q, corrNorm a M f t) := by
              rw [Finset.mul_sum]
    -- even split of the window
    have hEven := win_sum_even (Q := Q) (c := fun t => corrNorm a M f t) (corrNorm_neg f)
    have hWin : (∑ t ∈ win Q, corrNorm a M f t) = m + 2 * (∑ s ∈ posWinN Q, corrNorm a M f (s : ℤ)) := by
      calc
        (∑ t ∈ win Q, corrNorm a M f t) = corrNorm a M f 0 + 2 * (∑ s ∈ posWinN Q, corrNorm a M f (s : ℤ)) := hEven
        _ = m + 2 * (∑ s ∈ posWinN Q, corrNorm a M f (s : ℤ)) := by
              rw [corrNorm_zero]
    -- per-shift bounds on the positive window
    have hpos_le : (∑ s ∈ posWinN Q, corrNorm a M f (s : ℤ)) ≤
        C₂ * (m * A0 + 3 * B0) := by
      have hterm : ∀ s ∈ posWinN Q, corrNorm a M f (s : ℤ) ≤
          C₂ * ((((M - s : ℕ) : ℝ) * Real.sqrt ((s : ℝ) * l)) +
            (Real.sqrt ((s : ℝ) * l))⁻¹) := by
        intro s hs
        have hs1 : 1 ≤ s := by
          change s ∈ Finset.Icc 1 (Q - 1) at hs
          exact (Finset.mem_Icc.mp hs).1
        have hsM : s < M := by
          change s ∈ Finset.Icc 1 (Q - 1) at hs
          have hs2 : s ≤ Q - 1 := (Finset.mem_Icc.mp hs).2
          omega
        exact hC₂ (a := a) (M := M) hM f (l := l) hl hf hppp hs1 hsM
      have hpart1 : (∑ s ∈ posWinN Q, (((M - s : ℕ) : ℝ) * Real.sqrt ((s : ℝ) * l))) ≤ m * A0 := by
        calc
          (∑ s ∈ posWinN Q, (((M - s : ℕ) : ℝ) * Real.sqrt ((s : ℝ) * l)))
              ≤ ∑ s ∈ posWinN Q, m * Real.sqrt ((s : ℝ) * l) := by
                apply Finset.sum_le_sum
                intro s hs
                have hMs : ((M - s : ℕ) : ℝ) ≤ m := by
                  dsimp [m]
                  exact_mod_cast (Nat.sub_le M s)
                exact mul_le_mul_of_nonneg_right hMs (Real.sqrt_nonneg _)
          _ = m * (∑ s ∈ posWinN Q, Real.sqrt ((s : ℝ) * l)) := by rw [Finset.mul_sum]
          _ ≤ m * A0 := by
                have hs := sum_sqrt_posWinN_le Q hQ
                dsimp [A0]
                calc
                  m * (∑ s ∈ posWinN Q, Real.sqrt ((s : ℝ) * l))
                      = m * (Real.sqrt l * (∑ s ∈ posWinN Q, Real.sqrt (s : ℝ))) := by rw [sum_sqrt_mul_l Q l]
                  _ ≤ m * (Real.sqrt l * ((Q : ℝ) * Real.sqrt (Q : ℝ))) := by
                        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg l)) hm_nonneg
                  _ = m * (Real.sqrt l * (Q : ℝ) * Real.sqrt (Q : ℝ)) := by ring
          _ = m * A0 := by dsimp [A0]
      have hpart2 : (∑ s ∈ posWinN Q, (Real.sqrt ((s : ℝ) * l))⁻¹) ≤ 3 * B0 := by
        calc
          (∑ s ∈ posWinN Q, (Real.sqrt ((s : ℝ) * l))⁻¹)
              = (Real.sqrt l)⁻¹ * (∑ s ∈ posWinN Q, (Real.sqrt (s : ℝ))⁻¹) := sum_inv_sqrt_mul_l hl
          _ ≤ (Real.sqrt l)⁻¹ * (3 * Real.sqrt (Q : ℝ)) := by
                exact mul_le_mul_of_nonneg_left (sum_inv_sqrt_posWinN_le Q hQ)
                  (inv_nonneg.mpr (Real.sqrt_nonneg l))
          _ = 3 * (Real.sqrt l)⁻¹ * Real.sqrt (Q : ℝ) := by ring
          _ = 3 * B0 := by dsimp [B0]; ring
      have hsumraw : (∑ s ∈ posWinN Q,
            (((M - s : ℕ) : ℝ) * Real.sqrt ((s : ℝ) * l) + (Real.sqrt ((s : ℝ) * l))⁻¹)) ≤
          m * A0 + 3 * B0 := by
        rw [Finset.sum_add_distrib]
        exact add_le_add hpart1 hpart2
      calc
        (∑ s ∈ posWinN Q, corrNorm a M f (s : ℤ))
            ≤ ∑ s ∈ posWinN Q, C₂ * ((((M - s : ℕ) : ℝ) * Real.sqrt ((s : ℝ) * l)) +
                (Real.sqrt ((s : ℝ) * l))⁻¹) := by
              exact Finset.sum_le_sum hterm
        _ = C₂ * (∑ s ∈ posWinN Q,
            (((M - s : ℕ) : ℝ) * Real.sqrt ((s : ℝ) * l) + (Real.sqrt ((s : ℝ) * l))⁻¹)) := by rw [Finset.mul_sum]
        _ ≤ C₂ * (m * A0 + 3 * B0) := by
              exact mul_le_mul_of_nonneg_left hsumraw hC₂_nonneg
    -- fold constants: m + 2·(Σ c s) ≤ m + Csq·(m·A0 + B0)
    have h2le : m + 2 * (∑ s ∈ posWinN Q, corrNorm a M f (s : ℤ)) ≤ m + Csq * (m * A0 + B0) := by
      have hstep : 2 * (∑ s ∈ posWinN Q, corrNorm a M f (s : ℤ)) ≤ Csq * (m * A0 + B0) := by
        calc
          2 * (∑ s ∈ posWinN Q, corrNorm a M f (s : ℤ))
              ≤ 2 * (C₂ * (m * A0 + 3 * B0)) := mul_le_mul_of_nonneg_left hpos_le (by norm_num)
          _ = 2 * C₂ * (m * A0) + 6 * C₂ * B0 := by ring
          _ ≤ 6 * C₂ * (m * A0) + 6 * C₂ * B0 := by
                have hc1 : 2 * C₂ * (m * A0) ≤ 6 * C₂ * (m * A0) := by
                  have h6 : (2 : ℝ) * C₂ ≤ 6 * C₂ := by nlinarith [hC₂_nonneg]
                  exact mul_le_mul_of_nonneg_right h6 (mul_nonneg hm_nonneg hA0_nonneg)
                exact add_le_add hc1 le_rfl
          _ = (6 * C₂) * (m * A0 + B0) := by ring
          _ = Csq * (m * A0 + B0) := by rfl
      linarith
    calc
      (∑ t ∈ win Q, ((Q : ℝ) - ‖(t : ℝ)‖) * corrNorm a M f t)
          ≤ (Q : ℝ) * (∑ t ∈ win Q, corrNorm a M f t) := hw
      _ = (Q : ℝ) * (m + 2 * (∑ s ∈ posWinN Q, corrNorm a M f (s : ℤ))) := by rw [hWin]
      _ ≤ (Q : ℝ) * (m + Csq * (m * A0 + B0)) := by
            exact mul_le_mul_of_nonneg_left h2le (by positivity)
  -- assemble with the vdc second moment
  have hQpos : 0 < (Q : ℝ) := by positivity
  calc
    ‖∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)), uPhase a M f n‖ ^ 2
        ≤ ((m + (Q : ℝ)) / (Q : ℝ) ^ 2) *
            (∑ t ∈ win Q, ((Q : ℝ) - ‖(t : ℝ)‖) * corrNorm a M f t) := by
          have hvdc' := hvdc
          dsimp [m]
          simpa [win, corrNorm, corrSum] using hvdc'
    _ ≤ ((m + (Q : ℝ)) / (Q : ℝ) ^ 2) * ((Q : ℝ) * (m + Csq * (m * A0 + B0))) := by
          exact mul_le_mul_of_nonneg_left hMain0 (by positivity)
    _ = ((m + (Q : ℝ)) / (Q : ℝ)) * (m + Csq * (m * A0 + B0)) := by
          field_simp [hQpos.ne']
    _ = ((m + (Q : ℝ)) / (Q : ℝ)) *
          (m + Csq * ((m : ℝ) * Real.sqrt l * (Q : ℝ) * Real.sqrt (Q : ℝ) +
            (Real.sqrt l)⁻¹ * Real.sqrt (Q : ℝ))) := by
          dsimp [A0, B0]
          ring

end mid
end
open mid

theorem third_derivative_middle_bound {α : ℝ} (hα : 1 ≤ α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a : ℤ} {M : ℕ} (_hM : 2 ≤ M) (f : ℝ → ℝ) {l : ℝ} (_hl : 0 < l)
        (_hf : ContDiffOn ℝ 3 f (Set.Icc (a : ℝ) ((a : ℝ) + (M : ℝ))))
        (_hppp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + (M : ℝ)) →
          l ≤ deriv (deriv (deriv f)) x ∧ deriv (deriv (deriv f)) x ≤ α * l)
        (hlower : (1 : ℝ) ≤ (M : ℝ) ^ 3 * l) (hupper : l < 1),
        ‖∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)),
            Complex.exp (((2 * Real.pi * f (n : ℝ) : ℝ) : ℂ) * Complex.I)‖
          ≤ C * ((M : ℝ) * l ^ (1 / 6 : ℝ) +
              Real.sqrt (M : ℝ) * l ^ (-(1 / 6 : ℝ))) := by
  classical
  obtain ⟨Csq, hCsq_pos, hCsq⟩ := mid.vdc_sq (α := α) hα
  let C0 : ℝ := 2 * Real.sqrt (1 + Csq)
  have hC0_pos : 0 < C0 := by
    have h1 : 0 < 1 + Csq := by linarith
    dsimp [C0]
    exact mul_pos (by norm_num) (Real.sqrt_pos.mpr h1)
  refine ⟨C0, hC0_pos, ?_⟩
  intro a M hM2 f l hl hf hppp hlower hupper
  have hM : 1 ≤ M := by omega
  let S : ℂ := ∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)), uPhase a M f n
  let m : ℝ := (M : ℝ)
  let q : ℝ := l ^ (-(1 / 3 : ℝ))
  let Q : ℕ := ⌊q⌋₊
  have hm1 : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast hM
  have hmpos : 0 < m := by linarith
  have hm0 : 0 ≤ m := le_of_lt hmpos
  have hl0 : 0 ≤ l := le_of_lt hl
  have hzneg : (-(1 / 3 : ℝ)) < 0 := by norm_num
  have hq_gt_one : 1 < q := by
    have hlt := Real.rpow_lt_rpow_of_neg hl hupper hzneg
    dsimp [q]
    simpa using hlt
  have hq_pos : 0 < q := lt_trans zero_lt_one hq_gt_one
  have hq0 : 0 ≤ q := le_of_lt hq_pos
  have hq_ge_one : 1 ≤ q := le_of_lt hq_gt_one
  -- middle regime: `M^{-3} ≤ l`, hence `q = l^{-1/3} ≤ M`
  have hm3pos : 0 < (m : ℝ) ^ 3 := by positivity
  have hlm1 : (1 : ℝ) ≤ (m : ℝ) ^ 3 * l := by
    dsimp [m]
    exact hlower
  have hdiv : (1 : ℝ) / (m : ℝ) ^ 3 ≤ l := by
    rw [div_le_iff₀ hm3pos]
    rw [mul_comm]
    exact hlm1
  have hlm' : m ^ (-(3 : ℝ)) ≤ l := by
    rw [Real.rpow_neg (le_of_lt hmpos) (3 : ℝ)]
    rw [inv_eq_one_div]
    simpa using hdiv
  have hl3 : 0 < m ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hmpos (-(3 : ℝ))
  have hq_le_m : q ≤ m := by
    have hz : (-(1 / 3 : ℝ)) ≤ 0 := by norm_num
    have hle := Real.rpow_le_rpow_of_nonpos hl3 hlm' hz
    have hpow : (m ^ (-(3 : ℝ))) ^ (-(1 / 3 : ℝ)) = m := by
      calc
        (m ^ (-(3 : ℝ))) ^ (-(1 / 3 : ℝ)) = m ^ ((-(3 : ℝ)) * (-(1 / 3 : ℝ))) := by
          rw [← Real.rpow_mul hm0]
        _ = m ^ (1 : ℝ) := by congr 1; norm_num
        _ = m := by rw [Real.rpow_one]
    dsimp [q]
    rwa [hpow] at hle
  have hQ_ge_one_n : 1 ≤ Q := by
    dsimp [Q]
    exact Nat.le_floor (by exact_mod_cast hq_ge_one)
  have hQ_le_M : Q ≤ M := by
    dsimp [Q]
    have hfl : (⌊q⌋₊ : ℝ) ≤ q := Nat.floor_le hq0
    have h2 : (⌊q⌋₊ : ℝ) ≤ (M : ℝ) := by
      dsimp [m] at hq_le_m
      calc
        (⌊q⌋₊ : ℝ) ≤ q := hfl
        _ ≤ (M : ℝ) := hq_le_m
    exact_mod_cast h2
  have hQ_ge_one : 1 ≤ (Q : ℝ) := by exact_mod_cast hQ_ge_one_n
  have hQ_pos : 0 < (Q : ℝ) := by linarith
  have hq_le_2Q : q ≤ 2 * (Q : ℝ) := by
    have h1 : q < (Q : ℝ) + 1 := by simpa [Q] using (Nat.lt_floor_add_one q)
    linarith
  have hQ_le_q : (Q : ℝ) ≤ q := by
    dsimp [Q]
    exact Nat.floor_le hq0
  have hQ_nonneg : 0 ≤ (Q : ℝ) := le_of_lt hQ_pos
  have hsq : ‖S‖ ^ 2 ≤
      ((m + (Q : ℝ)) / (Q : ℝ)) * (m + Csq * (m * Real.sqrt l * (Q : ℝ) *
        Real.sqrt (Q : ℝ) + (Real.sqrt l)⁻¹ * Real.sqrt (Q : ℝ))) := by
    have hsq0 := hCsq (a := a) (M := M) hM f (Q := Q) hQ_ge_one_n hQ_le_M (l := l) hl hf hppp
    dsimp [S, m]
    simpa using hsq0
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hP : ((m + (Q : ℝ)) / (Q : ℝ)) ≤ 4 * m / q := by
    have h2 : (m + (Q : ℝ)) / (Q : ℝ) = m / (Q : ℝ) + 1 := by field_simp [hQ_pos.ne']
    have hmQ : m / (Q : ℝ) ≤ 2 * m / q := by
      calc
        m / (Q : ℝ) = (m * q) / ((Q : ℝ) * q) := by field_simp [hQ_pos.ne', hq_ne]
        _ ≤ (2 * m * (Q : ℝ)) / ((Q : ℝ) * q) := by
            apply div_le_div_of_nonneg_right
            · calc
                m * q ≤ m * (2 * (Q : ℝ)) := mul_le_mul_of_nonneg_left hq_le_2Q hm0
                _ = 2 * m * (Q : ℝ) := by ring
            · exact le_of_lt (mul_pos hQ_pos hq_pos)
        _ = 2 * m / q := by field_simp [hQ_pos.ne', hq_ne]
    have h1b : 1 ≤ 2 * m / q := by
      rw [le_div_iff₀ hq_pos]
      nlinarith [hq_le_m, hm0]
    calc
      (m + (Q : ℝ)) / (Q : ℝ) = m / (Q : ℝ) + 1 := h2
      _ ≤ 2 * m / q + 2 * m / q := by linarith
      _ = 4 * m / q := by ring
  have hqinv : q⁻¹ = l ^ (1 / 3 : ℝ) := by
    dsimp [q]
    calc
      (l ^ (-(1 / 3 : ℝ)))⁻¹ = ((l ^ (1 / 3 : ℝ))⁻¹)⁻¹ := by
        congr 1
        rw [Real.rpow_neg hl0]
      _ = l ^ (1 / 3 : ℝ) := by simp
  have hsqrt_nonneg : 0 ≤ Real.sqrt l := Real.sqrt_nonneg l
  have hAsqrt_q : Real.sqrt l * q * Real.sqrt q = 1 := by
    have hsqrt_l : Real.sqrt l = l ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow l
    have hsqrt_q : Real.sqrt q = q ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow q
    rw [hsqrt_l, hsqrt_q]
    dsimp [q]
    have hstep1 : (l ^ (-(1 / 3 : ℝ))) ^ (1 / 2 : ℝ) = l ^ (-(1 / 6 : ℝ)) := by
      calc
        (l ^ (-(1 / 3 : ℝ))) ^ (1 / 2 : ℝ) = l ^ ((-(1 / 3 : ℝ)) * (1 / 2 : ℝ)) := by
          rw [← Real.rpow_mul hl0]
        _ = l ^ (-(1 / 6 : ℝ)) := by congr 1; norm_num
    rw [hstep1]
    rw [← Real.rpow_add hl]
    rw [← Real.rpow_add hl]
    norm_num
  have hA_le1 : Real.sqrt l * (Q : ℝ) * Real.sqrt (Q : ℝ) ≤ 1 := by
    calc
      Real.sqrt l * (Q : ℝ) * Real.sqrt (Q : ℝ)
          ≤ Real.sqrt l * (Q : ℝ) * Real.sqrt q := by
              have hqsq : Real.sqrt (Q : ℝ) ≤ Real.sqrt q := Real.sqrt_le_sqrt hQ_le_q
              exact mul_le_mul_of_nonneg_left hqsq (mul_nonneg hsqrt_nonneg hQ_nonneg)
      _ ≤ Real.sqrt l * q * Real.sqrt q := by
              have h1 : Real.sqrt l * (Q : ℝ) ≤ Real.sqrt l * q :=
                mul_le_mul_of_nonneg_left hQ_le_q hsqrt_nonneg
              exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg q)
      _ = 1 := hAsqrt_q
  have hB_aux : (Real.sqrt l)⁻¹ * Real.sqrt q = q ^ 2 := by
    have hsqrt_l : Real.sqrt l = l ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow l
    have hsqrt_q : Real.sqrt q = q ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow q
    rw [hsqrt_l, hsqrt_q]
    dsimp [q]
    have hneg : (l ^ (1 / 2 : ℝ))⁻¹ = l ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg hl0]
    rw [hneg]
    have hstep1 : (l ^ (-(1 / 3 : ℝ))) ^ (1 / 2 : ℝ) = l ^ (-(1 / 6 : ℝ)) := by
      calc
        (l ^ (-(1 / 3 : ℝ))) ^ (1 / 2 : ℝ) = l ^ ((-(1 / 3 : ℝ)) * (1 / 2 : ℝ)) := by
          rw [← Real.rpow_mul hl0]
        _ = l ^ (-(1 / 6 : ℝ)) := by congr 1; norm_num
    rw [hstep1]
    have htwo : (l ^ (-(1 / 3 : ℝ))) ^ 2 = l ^ (-(2 / 3 : ℝ)) := by
      rw [pow_two]
      rw [← Real.rpow_add hl]
      congr 1
      norm_num
    rw [htwo]
    rw [← Real.rpow_add hl]
    congr 1
    norm_num
  have hB_le : (Real.sqrt l)⁻¹ * Real.sqrt (Q : ℝ) ≤ q ^ 2 := by
    calc
      (Real.sqrt l)⁻¹ * Real.sqrt (Q : ℝ)
          ≤ (Real.sqrt l)⁻¹ * Real.sqrt q := by
              exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hQ_le_q)
                (inv_nonneg.mpr hsqrt_nonneg)
      _ = q ^ 2 := hB_aux
  have hCsq0 : 0 ≤ Csq := le_of_lt hCsq_pos
  have hbracket : m + Csq * (m * (Real.sqrt l * (Q : ℝ) * Real.sqrt (Q : ℝ)) +
        (Real.sqrt l)⁻¹ * Real.sqrt (Q : ℝ))
      ≤ m + Csq * (m + q ^ 2) := by
    have hmA : m * (Real.sqrt l * (Q : ℝ) * Real.sqrt (Q : ℝ)) ≤ m := by
      calc
        m * (Real.sqrt l * (Q : ℝ) * Real.sqrt (Q : ℝ)) ≤ m * 1 := by
          exact mul_le_mul_of_nonneg_left hA_le1 hm0
        _ = m := by ring
    have hB' : (Real.sqrt l)⁻¹ * Real.sqrt (Q : ℝ) ≤ q ^ 2 := hB_le
    have hin : m * (Real.sqrt l * (Q : ℝ) * Real.sqrt (Q : ℝ)) +
          (Real.sqrt l)⁻¹ * Real.sqrt (Q : ℝ) ≤ m + q ^ 2 := by linarith
    have hCsq_inner : Csq * (m * (Real.sqrt l * (Q : ℝ) * Real.sqrt (Q : ℝ)) +
          (Real.sqrt l)⁻¹ * Real.sqrt (Q : ℝ)) ≤ Csq * (m + q ^ 2) :=
      mul_le_mul_of_nonneg_left hin hCsq0
    linarith
  have hbracket0 : 0 ≤ m + Csq * (m + q ^ 2) := by
    have hqsq : 0 ≤ q ^ 2 := sq_nonneg q
    have h2 : 0 ≤ m + q ^ 2 := by linarith
    have h3 : 0 ≤ Csq * (m + q ^ 2) := mul_nonneg hCsq0 h2
    linarith
  have hP0 : 0 ≤ (m + (Q : ℝ)) / (Q : ℝ) := by
    have hnum : 0 ≤ m + (Q : ℝ) := by
      have : 0 ≤ m := hm0
      have : 0 ≤ (Q : ℝ) := hQ_nonneg
      linarith
    exact div_nonneg hnum (le_of_lt hQ_pos)
  have hsq2 : ‖S‖ ^ 2 ≤ (4 * m / q) * (m + Csq * (m + q ^ 2)) := by
    calc
      ‖S‖ ^ 2 ≤ ((m + (Q : ℝ)) / (Q : ℝ)) *
          (m + Csq * (m * Real.sqrt l * (Q : ℝ) * Real.sqrt (Q : ℝ) +
              (Real.sqrt l)⁻¹ * Real.sqrt (Q : ℝ))) := hsq
      _ = ((m + (Q : ℝ)) / (Q : ℝ)) *
          (m + Csq * (m * (Real.sqrt l * (Q : ℝ) * Real.sqrt (Q : ℝ)) +
              (Real.sqrt l)⁻¹ * Real.sqrt (Q : ℝ))) := by ring
      _ ≤ ((m + (Q : ℝ)) / (Q : ℝ)) * (m + Csq * (m + q ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hbracket hP0
      _ ≤ (4 * m / q) * (m + Csq * (m + q ^ 2)) := by
          exact mul_le_mul_of_nonneg_right hP hbracket0
  have hrewr : (4 * m / q) * (m + Csq * (m + q ^ 2))
      = 4 * (1 + Csq) * m ^ 2 * (q⁻¹) + 4 * Csq * m * q := by
    field_simp [hq_ne]
    ring
  have hmain : ‖S‖ ^ 2 ≤ 4 * (1 + Csq) * m ^ 2 * l ^ (1 / 3 : ℝ) + 4 * Csq * m * q := by
    calc
      ‖S‖ ^ 2 ≤ (4 * m / q) * (m + Csq * (m + q ^ 2)) := hsq2
      _ = 4 * (1 + Csq) * m ^ 2 * (q⁻¹) + 4 * Csq * m * q := hrewr
      _ = 4 * (1 + Csq) * m ^ 2 * l ^ (1 / 3 : ℝ) + 4 * Csq * m * q := by rw [hqinv]
  have hl3pos : 0 < l ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hl (1 / 3 : ℝ)
  have hsqrt_l3 : Real.sqrt (l ^ (1 / 3 : ℝ)) = l ^ (1 / 6 : ℝ) := by
    calc
      Real.sqrt (l ^ (1 / 3 : ℝ)) = (l ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      _ = l ^ ((1 / 3 : ℝ) * (1 / 2 : ℝ)) := by
        rw [← Real.rpow_mul hl0]
      _ = l ^ (1 / 6 : ℝ) := by congr 1; norm_num
  have hsqrt_q6 : Real.sqrt q = l ^ (-(1 / 6 : ℝ)) := by
    calc
      Real.sqrt q = q ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow q
      _ = l ^ (-(1 / 6 : ℝ)) := by
        dsimp [q]
        calc
          (l ^ (-(1 / 3 : ℝ))) ^ (1 / 2 : ℝ) = l ^ ((-(1 / 3 : ℝ)) * (1 / 2 : ℝ)) := by
            rw [← Real.rpow_mul hl0]
          _ = l ^ (-(1 / 6 : ℝ)) := by congr 1; norm_num
  let xA : ℝ := 2 * Real.sqrt (1 + Csq) * (m * Real.sqrt (l ^ (1 / 3 : ℝ)))
  let xB : ℝ := 2 * Real.sqrt Csq * (Real.sqrt m * Real.sqrt q)
  have hsqrt1pC : 0 ≤ Real.sqrt (1 + Csq) := Real.sqrt_nonneg (1 + Csq)
  have ha0 : 0 ≤ xA := by
    dsimp [xA]
    exact mul_nonneg (mul_nonneg (by norm_num) hsqrt1pC)
      (mul_nonneg hm0 (Real.sqrt_nonneg (l ^ (1 / 3 : ℝ))))
  have hb0 : 0 ≤ xB := by
    dsimp [xB]
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg Csq))
      (mul_nonneg (Real.sqrt_nonneg m) (Real.sqrt_nonneg q))
  have hx0 : 0 ≤ ‖S‖ := norm_nonneg S
  have hsq_parts : (xA ^ 2 + xB ^ 2) =
        4 * (1 + Csq) * m ^ 2 * l ^ (1 / 3 : ℝ) + 4 * Csq * m * q := by
    dsimp [xA, xB]
    have h1 : (Real.sqrt (1 + Csq)) ^ 2 = 1 + Csq := Real.sq_sqrt (by linarith : 0 ≤ 1 + Csq)
    have h2 : (Real.sqrt (l ^ (1 / 3 : ℝ))) ^ 2 = l ^ (1 / 3 : ℝ) := Real.sq_sqrt (le_of_lt hl3pos)
    have h3 : (Real.sqrt Csq) ^ 2 = Csq := Real.sq_sqrt hCsq0
    have h4 : (Real.sqrt m) ^ 2 = m := Real.sq_sqrt hm0
    have h5 : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq0
    ring_nf
    rw [h1, h2, h3, h4, h5]
    ring
  have hle_of_sq : ‖S‖ ≤ xA + xB := by
    have hab : 0 ≤ xA + xB := add_nonneg ha0 hb0
    have hab2 : (xA + xB) ^ 2 = xA ^ 2 + xB ^ 2 + 2 * xA * xB := by ring
    have hnon : 0 ≤ 2 * xA * xB := by positivity
    have hx2 : ‖S‖ ^ 2 ≤ (xA + xB) ^ 2 := by
      calc
        ‖S‖ ^ 2 ≤ xA ^ 2 + xB ^ 2 := by
              rw [hsq_parts]
              exact hmain
        _ ≤ (xA + xB) ^ 2 := by rw [hab2]; linarith
    exact le_of_sq_le_sq hx2 hab
  have hCsq_le : Real.sqrt Csq ≤ Real.sqrt (1 + Csq) := Real.sqrt_le_sqrt (by linarith)
  have hsqrtm0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  have hnl6 : 0 ≤ l ^ (-(1 / 6 : ℝ)) := le_of_lt (Real.rpow_pos_of_pos hl (-(1 / 6 : ℝ)))
  have hab : xA + xB ≤ C0 * (m * l ^ (1 / 6 : ℝ) + Real.sqrt m * l ^ (-(1 / 6 : ℝ))) := by
    have hpart1 : xA ≤ 2 * Real.sqrt (1 + Csq) * (m * l ^ (1 / 6 : ℝ)) := by
      dsimp [xA]
      rw [hsqrt_l3]
    have hpart2 : xB ≤ 2 * Real.sqrt (1 + Csq) * (Real.sqrt m * l ^ (-(1 / 6 : ℝ))) := by
      dsimp [xB]
      rw [hsqrt_q6]
      have h2l : 2 * Real.sqrt Csq ≤ 2 * Real.sqrt (1 + Csq) :=
        mul_le_mul_of_nonneg_left hCsq_le (by norm_num)
      exact mul_le_mul h2l (le_rfl) (mul_nonneg hsqrtm0 hnl6) (mul_nonneg (by norm_num) hsqrt1pC)
    calc
      xA + xB ≤ 2 * Real.sqrt (1 + Csq) * (m * l ^ (1 / 6 : ℝ))
            + 2 * Real.sqrt (1 + Csq) * (Real.sqrt m * l ^ (-(1 / 6 : ℝ))) := by linarith
      _ = 2 * Real.sqrt (1 + Csq) * (m * l ^ (1 / 6 : ℝ) + Real.sqrt m * l ^ (-(1 / 6 : ℝ))) := by ring
      _ = C0 * (m * l ^ (1 / 6 : ℝ) + Real.sqrt m * l ^ (-(1 / 6 : ℝ))) := by
          dsimp [C0]
  have hSbound : ‖S‖ ≤ C0 * (m * l ^ (1 / 6 : ℝ) + Real.sqrt m * l ^ (-(1 / 6 : ℝ))) := by
    exact le_trans hle_of_sq hab
  -- convert from the block phase to the plain phase sum
  have hSsum : (∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)),
      Complex.exp (((2 * Real.pi * f (n : ℝ) : ℝ) : ℂ) * Complex.I)) = S := by
    dsimp [S]
    simpa [eR] using (uPhase_sum_eq f).symm
  calc
    ‖∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)),
        Complex.exp (((2 * Real.pi * f (n : ℝ) : ℝ) : ℂ) * Complex.I)‖
        = ‖S‖ := by rw [hSsum]
    _ ≤ C0 * (m * l ^ (1 / 6 : ℝ) + Real.sqrt m * l ^ (-(1 / 6 : ℝ))) := hSbound
    _ = C0 * ((M : ℝ) * l ^ (1 / 6 : ℝ) + Real.sqrt (M : ℝ) * l ^ (-(1 / 6 : ℝ))) := by
        simp [m]


end Commons.Analysis.ExponentialSums


