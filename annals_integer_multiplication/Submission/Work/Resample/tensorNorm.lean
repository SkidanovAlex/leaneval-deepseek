import Mathlib
import Submission.Work.Resample.defs

/-!
# Operator norm of a tensor (Kronecker) product of matrices

`tensorFun ss ts f` is the tensor product `⊗ᵢ Aᵢ` of the one-dimensional matrices
`Aᵢ = (f i j k)_{jk}`, acting on flat lexicographic (mixed-radix digit) arrays.
If every `Aᵢ` maps the sup-norm ball of radius `cᵢ` into itself, then the tensor
product maps the sup-norm ball of radius `∏ᵢ cᵢ` into itself.

The proof proceeds by induction on the list of factors: writing `u` as a stack of
`s` blocks of length `ss'.prod`, the tensor map first applies the tensor of the
remaining factors to each block, and then the first matrix `A₀` to the resulting
stack of second coordinates.  Both steps are bounded directly by the hypothesis
`hm` (resp. the induction hypothesis), so no operator-norm machinery is needed.
-/

set_option autoImplicit false

namespace Work.Resample

open scoped BigOperators

/-! ### Elementary list and sup-norm lemmas -/

lemma prod_map_range_eq {M : Type*} [CommMonoid M] (g : ℕ → M) (n : ℕ) :
    ((List.range n).map g).prod = ∏ i ∈ Finset.range n, g i := by
  rw [← List.prod_toFinset (l := List.range n) g List.nodup_range, List.toFinset_range]

lemma prod_map_range_succ' {M : Type*} [CommMonoid M] (g : ℕ → M) (n : ℕ) :
    ((List.range (n + 1)).map g).prod = g 0 * ((List.range n).map (fun i => g (i + 1))).prod := by
  rw [prod_map_range_eq g (n + 1), prod_map_range_eq (fun i => g (i + 1)) n,
      Finset.prod_range_succ',
      show (∏ i ∈ Finset.range n, g (i + 1)) = ∏ i ∈ Finset.range n, g (1 + i) by
        exact Finset.prod_congr rfl fun i _ => by rw [add_comm]]
  exact (mul_comm _ _)

/-- Sup-norm bound for a function: it suffices to bound every value. -/
lemma norm_pi_le {ι : Type*} [Fintype ι] [Nonempty ι] {E : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] (f : ∀ i, E i) {a : ℝ} (h : ∀ i, ‖f i‖ ≤ a) :
    ‖f‖ ≤ a := by
  have ha : 0 ≤ a := le_trans (norm_nonneg _) (h (Classical.arbitrary ι))
  have key : (Finset.univ.sup fun i => ‖f i‖₊) ≤ (⟨a, ha⟩ : NNReal) :=
    Finset.sup_le fun i _ => by exact_mod_cast h i
  calc ‖f‖ = ((Finset.univ.sup fun i => ‖f i‖₊ : NNReal) : ℝ) := Pi.norm_def f
    _ ≤ ((⟨a, ha⟩ : NNReal) : ℝ) := NNReal.coe_le_coe.mpr key
    _ = a := rfl

/-- Norm of a constant function. -/
lemma norm_const_pi {ι : Type*} [Fintype ι] [Nonempty ι] (z : ℂ) :
    ‖(fun _ : ι => z)‖ = ‖z‖ := by
  rw [Pi.norm_def, Finset.sup_const Finset.univ_nonempty]
  simp

/-- In a list of positive product, every entry is positive. -/
lemma getD_pos_of_prod_pos {ss : List ℕ} (h : 0 < ss.prod) (i : ℕ) (hi : i < ss.length) :
    0 < ss.getD i 0 := by
  rw [List.getD_eq_getElem _ _ hi]
  have hmem : ss[i] ∈ ss := List.getElem_mem hi
  have hne : ss[i] ≠ 0 := by
    intro h0
    have : ss.prod = 0 := List.prod_eq_zero_iff.mpr (h0 ▸ hmem)
    omega
  omega

/-! ### Splitting off the first factor -/

lemma digitProd_cons_head (s : ℕ) (ss' : List ℕ) (t : ℕ) (ts' : List ℕ)
    (f : ℕ → ℕ → ℕ → ℂ) (A B : ℕ) :
    digitProd (s :: ss') (t :: ts') f A B =
      f 0 (A / ts'.prod % t) (B / ss'.prod % s) *
        digitProd ss' ts' (fun i => f (i+1)) (A % ts'.prod) (B % ss'.prod) := by
  simp only [digitProd, List.length_cons, prod_map_range_succ']
  simp [HvdH.digits]

/-- The tensor product splits off its first factor: applying it at the index
`(j₀, J')` amounts to applying the matrix `f 0` to the stack of values of the
tensor product of the remaining factors. -/
lemma tensorFun_cons (s : ℕ) (ss' : List ℕ) (t : ℕ) (ts' : List ℕ)
    (hS : 0 < ss'.prod) (hT : 0 < ts'.prod)
    (f : ℕ → ℕ → ℕ → ℂ) (u : Fin (s * ss'.prod) → ℂ)
    (j₀ : Fin t) (J' : Fin ts'.prod) :
    tensorFun (s :: ss') (t :: ts') f u (finProdFinEquiv (j₀, J')) =
      ∑ k : Fin s, f 0 j₀ k *
        tensorFun ss' ts' (fun i => f (i+1)) (fun K'' => u (finProdFinEquiv (k, K''))) J' := by
  have hA : ((finProdFinEquiv (j₀, J') : Fin (t * ts'.prod)) : ℕ) =
      (J' : ℕ) + ts'.prod * (j₀ : ℕ) := finProdFinEquiv_apply_val _
  have hB : ∀ (k : Fin s) (K'' : Fin ss'.prod),
      ((finProdFinEquiv (k, K'') : Fin (s * ss'.prod)) : ℕ) =
        (K'' : ℕ) + ss'.prod * (k : ℕ) := fun k K'' => finProdFinEquiv_apply_val _
  have step : ∀ (k : Fin s) (K'' : Fin ss'.prod),
      digitProd (s :: ss') (t :: ts') f ((finProdFinEquiv (j₀, J') : Fin (t * ts'.prod)) : ℕ)
        ((finProdFinEquiv (k, K'') : Fin (s * ss'.prod)) : ℕ) =
        f 0 (j₀ : ℕ) (k : ℕ) * digitProd ss' ts' (fun i => f (i+1)) (J' : ℕ) (K'' : ℕ) := by
    intro k K''
    rw [digitProd_cons_head, hB k K'', hA]
    have h1 : ((J' : ℕ) + ts'.prod * (j₀ : ℕ)) / ts'.prod % t = (j₀ : ℕ) := by
      rw [Nat.add_mul_div_left _ _ hT, Nat.div_eq_of_lt J'.isLt, Nat.zero_add,
        Nat.mod_eq_of_lt j₀.isLt]
    have h2 : ((K'' : ℕ) + ss'.prod * (k : ℕ)) / ss'.prod % s = (k : ℕ) := by
      rw [Nat.add_mul_div_left _ _ hS, Nat.div_eq_of_lt K''.isLt, Nat.zero_add,
        Nat.mod_eq_of_lt k.isLt]
    have h3 : ((J' : ℕ) + ts'.prod * (j₀ : ℕ)) % ts'.prod = (J' : ℕ) := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt J'.isLt]
    have h4 : ((K'' : ℕ) + ss'.prod * (k : ℕ)) % ss'.prod = (K'' : ℕ) := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt K''.isLt]
    rw [h1, h2, h3, h4]
  have step2 : ∀ (k : Fin s) (K'' : Fin ss'.prod),
      digitProd (s :: ss') (t :: ts') f ((finProdFinEquiv (j₀, J') : Fin (t * ts'.prod)) : ℕ)
        ((finProdFinEquiv (k, K'') : Fin (s * ss'.prod)) : ℕ) * u (finProdFinEquiv (k, K'')) =
        f 0 (j₀ : ℕ) (k : ℕ) * (digitProd ss' ts' (fun i => f (i+1)) (J' : ℕ) (K'' : ℕ) *
          u (finProdFinEquiv (k, K''))) := by
    intro k K''
    rw [step k K'']; ring
  have hL : tensorFun (s :: ss') (t :: ts') f u (finProdFinEquiv (j₀, J')) =
      ∑ K : Fin (s * ss'.prod), digitProd (s :: ss') (t :: ts') f
        ((finProdFinEquiv (j₀, J') : Fin (t * ts'.prod)) : ℕ) (K : ℕ) * u K := rfl
  rw [hL]
  simp only [tensorFun]
  rw [← Equiv.sum_comp finProdFinEquiv
    (fun K : Fin (s * ss'.prod) => digitProd (s :: ss') (t :: ts') f
      ((finProdFinEquiv (j₀, J') : Fin (t * ts'.prod)) : ℕ) (K : ℕ) * u K)]
  rw [Finset.sum_congr rfl (fun p _ => step2 p.1 p.2)]
  simp only [Finset.mul_sum]
  have hcombine : (∑ p : Fin s × Fin ss'.prod, f 0 (j₀ : ℕ) (p.1 : ℕ) *
      (digitProd ss' ts' (fun i => f (i+1)) (J' : ℕ) (p.2 : ℕ) * u (finProdFinEquiv p)))
      = ∑ x : Fin s, ∑ y : Fin ss'.prod, f 0 (j₀ : ℕ) (x : ℕ) *
        (digitProd ss' ts' (fun i => f (i+1)) (J' : ℕ) (y : ℕ) * u (finProdFinEquiv (x, y))) :=
    Fintype.sum_prod_type _
  rw [hcombine]

/-! ### The main induction -/

/-- Norm bound for the tensor product, under the additional hypotheses that the
digit lengths are positive and that all the constants are nonnegative. -/
theorem tensorNorm_aux : ∀ (ss ts : List ℕ), ts.length = ss.length → 0 < ss.prod →
    0 < ts.prod → ∀ (f : ℕ → ℕ → ℕ → ℂ) (c : ℕ → ℝ),
      (∀ i < ss.length, ∀ x : Fin (ss.getD i 0) → ℂ,
        ‖(fun j : Fin (ts.getD i 0) => ∑ k : Fin (ss.getD i 0), f i (j : ℕ) (k : ℕ) * x k)‖ ≤
          c i * ‖x‖) →
      (∀ i < ss.length, 0 ≤ c i) → ∀ u : Fin ss.prod → ℂ,
      ‖tensorFun ss ts f u‖ ≤ ((List.range ss.length).map c).prod * ‖u‖ := by
  intro ss
  induction ss with
  | nil =>
    intro ts hl hspos htpos f c hm hc u
    rw [List.length_nil] at hl
    obtain rfl : ts = [] := List.length_eq_zero_iff.mp hl
    simp only [List.prod_nil, List.length_nil, List.range_zero, List.map_nil] at u ⊢
    show ‖(fun _ : Fin 1 => ∑ K : Fin 1, (1 : ℂ) * u K)‖ ≤ 1 * ‖u‖
    rw [Fin.sum_univ_one, norm_const_pi]
    simp only [one_mul]
    exact norm_le_pi_norm u 0
  | cons s ss' ih =>
    intro ts hl hspos htpos f c hm hc u
    cases ts with
    | nil => simp at hl
    | cons t ts' =>
      have hTS : ts'.length = ss'.length := by
        simp only [List.length_cons] at hl
        omega
      have hs : 0 < s := Nat.pos_of_mul_pos_right (show (0 : ℕ) < s * ss'.prod from hspos)
      have hS : 0 < ss'.prod := Nat.pos_of_mul_pos_left (show (0 : ℕ) < s * ss'.prod from hspos)
      have ht : 0 < t := Nat.pos_of_mul_pos_right (show (0 : ℕ) < t * ts'.prod from htpos)
      have hT : 0 < ts'.prod := Nat.pos_of_mul_pos_left (show (0 : ℕ) < t * ts'.prod from htpos)
      have hsne : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
      have hSne : Nonempty (Fin ss'.prod) := ⟨⟨0, hS⟩⟩
      have hTne : Nonempty (Fin ts'.prod) := ⟨⟨0, hT⟩⟩
      have htne : Nonempty (Fin ((t :: ts').prod)) :=
        ⟨⟨0, show 0 < (t :: ts').prod from Nat.mul_pos ht hT⟩⟩
      have hc0 : 0 ≤ c 0 := hc 0 (by simp [List.length_cons])
      have hm' : ∀ i < ss'.length, ∀ x : Fin (ss'.getD i 0) → ℂ,
          ‖(fun j : Fin (ts'.getD i 0) => ∑ k : Fin (ss'.getD i 0),
              f (i + 1) (j : ℕ) (k : ℕ) * x k)‖ ≤ c (i + 1) * ‖x‖ := by
        intro i hi x
        exact hm (i + 1) (by simp [List.length_cons]; omega) x
      have hc' : ∀ i < ss'.length, 0 ≤ c (i + 1) := by
        intro i hi
        exact hc (i + 1) (by simp [List.length_cons]; omega)
      have hPnn : 0 ≤ ((List.range ss'.length).map (fun i => c (i + 1))).prod := by
        apply List.prod_nonneg
        intro a ha
        rw [List.mem_map] at ha
        obtain ⟨i, hi, rfl⟩ := ha
        exact hc' i (List.mem_range.mp hi)
      have hm0 : ∀ x : Fin s → ℂ,
          ‖(fun j : Fin t => ∑ k : Fin s, f 0 (j : ℕ) (k : ℕ) * x k)‖ ≤ c 0 * ‖x‖ := by
        intro x
        exact hm 0 (by simp [List.length_cons]) x
      have hpt : ∀ (j₀ : Fin t) (J' : Fin ts'.prod),
          ‖tensorFun (s :: ss') (t :: ts') f u (finProdFinEquiv (j₀, J'))‖ ≤
            c 0 * (((List.range ss'.length).map (fun i => c (i + 1))).prod * ‖u‖) := by
        intro j₀ J'
        rw [tensorFun_cons s ss' t ts' hS hT f u j₀ J']
        have hxk : ‖(fun k : Fin s => tensorFun ss' ts' (fun i => f (i + 1))
              (fun K'' => u (finProdFinEquiv (k, K''))) J')‖ ≤
            ((List.range ss'.length).map (fun i => c (i + 1))).prod * ‖u‖ := by
          apply norm_pi_le
          intro k
          have hblk : ‖(fun K'' : Fin ss'.prod => u (finProdFinEquiv (k, K'')))‖ ≤ ‖u‖ := by
            apply norm_pi_le
            intro K''
            exact norm_le_pi_norm u _
          have hih := ih ts' hTS hS hT (fun i => f (i + 1)) (fun i => c (i + 1)) hm' hc'
            (fun K'' : Fin ss'.prod => u (finProdFinEquiv (k, K'')))
          calc ‖(fun k' : Fin s => tensorFun ss' ts' (fun i => f (i + 1))
                  (fun K'' => u (finProdFinEquiv (k', K''))) J') k‖
              = ‖tensorFun ss' ts' (fun i => f (i + 1))
                  (fun K'' => u (finProdFinEquiv (k, K''))) J'‖ := rfl
            _ ≤ ‖tensorFun ss' ts' (fun i => f (i + 1))
                  (fun K'' => u (finProdFinEquiv (k, K'')))‖ := norm_le_pi_norm _ _
            _ ≤ ((List.range ss'.length).map (fun i => c (i + 1))).prod *
                  ‖(fun K'' : Fin ss'.prod => u (finProdFinEquiv (k, K'')))‖ := hih
            _ ≤ ((List.range ss'.length).map (fun i => c (i + 1))).prod * ‖u‖ :=
                  mul_le_mul_of_nonneg_left hblk hPnn
        exact le_trans (norm_le_pi_norm (fun j : Fin t => ∑ k : Fin s, f 0 (j : ℕ) (k : ℕ) *
            tensorFun ss' ts' (fun i => f (i + 1)) (fun K'' => u (finProdFinEquiv (k, K''))) J') j₀)
          (le_trans (hm0 _) (mul_le_mul_of_nonneg_left hxk hc0))
      have hmain : ‖tensorFun (s :: ss') (t :: ts') f u‖ ≤
          c 0 * (((List.range ss'.length).map (fun i => c (i + 1))).prod * ‖u‖) := by
        apply norm_pi_le
        intro J
        rw [← Equiv.apply_symm_apply finProdFinEquiv J]
        exact hpt _ _
      have hprod : ((List.range (s :: ss').length).map c).prod =
          c 0 * ((List.range ss'.length).map (fun i => c (i + 1))).prod := by
        rw [List.length_cons]
        exact prod_map_range_succ' c ss'.length
      rw [hprod]
      refine le_trans hmain (le_of_eq ?_)
      ring

/-- **Tensor norm bound.**  If the one-dimensional factor `f i` is bounded by `c i`
on the sup-norm unit balls, then their tensor product is bounded by `∏ᵢ c i`. -/
theorem tensorNorm (ss ts : List ℕ) (hl : ts.length = ss.length)
    (f : ℕ → ℕ → ℕ → ℂ) (c : ℕ → ℝ)
    (hm : ∀ i < ss.length, ∀ x : Fin (ss.getD i 0) → ℂ,
      ‖(fun j : Fin (ts.getD i 0) => ∑ k : Fin (ss.getD i 0), f i (j : ℕ) (k : ℕ) * x k)‖ ≤ c i * ‖x‖)
    (u : Fin ss.prod → ℂ) :
    ‖Work.Resample.tensorFun ss ts f u‖ ≤ ((List.range ss.length).map c).prod * ‖u‖ := by
  by_cases hs : ss.prod = 0
  · have hzero : tensorFun ss ts f u = 0 := by
      funext J
      refine Finset.sum_eq_zero (fun K _ => ?_)
      exact absurd (K.isLt : (K : ℕ) < ss.prod) (by simp [hs])
    have hnorm : ‖u‖ = 0 := by
      have hu : u = 0 := by
        funext x
        exact absurd x.isLt (by simp [hs])
      rw [hu, norm_zero]
    rw [hzero, norm_zero, hnorm, mul_zero]
  · have hspos : 0 < ss.prod := Nat.pos_of_ne_zero hs
    have hcpos : ∀ i < ss.length, 0 ≤ c i := by
      intro i hi
      have hgt : 0 < ss.getD i 0 := getD_pos_of_prod_pos hspos i hi
      have : Nonempty (Fin (ss.getD i 0)) := ⟨⟨0, hgt⟩⟩
      have hkey : ‖(fun _ : Fin (ss.getD i 0) => (1 : ℂ))‖ = (1 : ℝ) := by
        rw [norm_const_pi]
        norm_num
      have h1 : 0 ≤ c i * ‖(fun _ : Fin (ss.getD i 0) => (1 : ℂ))‖ :=
        le_trans (norm_nonneg _) (hm i hi (fun _ : Fin (ss.getD i 0) => (1 : ℂ)))
      rw [hkey, mul_one] at h1
      exact h1
    by_cases ht : ts.prod = 0
    · have hzero : tensorFun ss ts f u = 0 := by
        funext J
        exact absurd (J.isLt : (J : ℕ) < ts.prod) (by simp [ht])
      have hP : 0 ≤ ((List.range ss.length).map c).prod := by
        apply List.prod_nonneg
        intro a ha
        rw [List.mem_map] at ha
        obtain ⟨i, hi, rfl⟩ := ha
        exact hcpos i (List.mem_range.mp hi)
      rw [hzero, norm_zero]
      exact mul_nonneg hP (norm_nonneg u)
    · exact tensorNorm_aux ss ts hl hspos (Nat.pos_of_ne_zero ht) f c hm hcpos u

end Work.Resample
