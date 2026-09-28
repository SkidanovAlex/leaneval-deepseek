import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.box_card
import Submission.Work.HP.prim_box_lower
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.primCount_residue_le

/-!
# N01: height balls are finite and contain `≫ A^N` primitive vectors

Node N01 of the Browning--Le Boudec--Sawin formalisation (see `DESIGN.md`).  The main
statement `count_basic` proves that every height ball `primSet d n A P` is finite and that
the number of primitive coefficient vectors of height `≤ A` grows like `A^{N_{d,n}}`.

Supporting lemmas (proved in sibling modules and imported here):

* `box_card` -- the coordinate box `∏_m [-B,B]` has `(2B+1)^N` elements, and its
  `g`-divisible vectors are in bijection with the box of radius `B/g`;
* `prim_box_lower` -- a lower bound for the number of primitive vectors in a box, by
  removing the zero vector and the (at most `Σ_g (2⌊B/g⌋+1)^N`) non-primitive ones;
* `sum_div_bound_aux` (private, proved below) -- that sum is at most a quarter of the
  leading term `(2B)^N`, via `2⌊B/g⌋+1 ≤ 3B/g`, the bound `1/g^N ≤ 2^{-(N-6)}/g^6` and the
  `5`-th-power telescoping estimate `Σ_{g≥2} 1/g^6 ≤ 1/64 + 1/729 + 1/486`;
* `six_le_NN` -- `N_{d,n} ≥ 6` when `2 ≤ d ≤ n`;
* `primCount_residue_le` -- the residue-class bound used by the sibling nodes N11, N13, N14.
-/

namespace Work.HP

open Filter Finset

/-!
## N01: height balls are finite and contain `≫ A^N` primitive vectors

**Finiteness.** `primSet d n A P` is contained in the coordinate box `∏_m [-⌈A⌉, ⌈A⌉]`,
because every coordinate of an integer vector is bounded by its Euclidean norm, and
`eNorm a ≤ A ≤ ⌈A⌉`.

**Lower bound.** Count inside the coordinate box of radius `B = ⌊A/√N⌋`, which is contained in
the Euclidean ball of radius `A` (since `B √N ≤ A`).  A vector of the box is either zero,
primitive, or non-primitive and non-zero; in the last case its gcd divides every coordinate and
satisfies `2 ≤ gcd(a) ≤ B`.  Hence

`#(primitive vectors of box B) ≥ #box(B) - 1 - Σ_{g=2}^{B} #(box(B) ∩ gℤ^N)`  (`prim_box_lower`),

while `#(box(B) ∩ gℤ^N) = (2⌊B/g⌋+1)^N` (`box_card`).  The sum is at most `(2B)^N/4`
(`sum_div_bound_aux`, using `N ≥ 6`), so `#prim(box B) ≥ (1/2)(2B)^N`.  Since `N ≥ 6` whenever
`2 ≤ d ≤ n` (`six_le_NN`) and `2B ≥ A/√N`, this gives `≫ A^N`.

The residue-class bound `primCount d n A (a ≡ b mod q) ≤ (2A/q+1)^N` used by the sibling
nodes N11, N13 and N14 is proved in `Submission/Work/HP/primCount_residue_le.lean` and
re-exported here.

**Conclusion.** With `B = ⌊A/√N⌋ ≥ 5` one gets
`primCount d n A (fun _ => True) ≥ (1/2)(2B)^N ≥ A^N/(2(√N)^N)`, so the constant
`c = 1/(2(√N)^N)` works.
-/

variable {d n : ℕ}

/-- Every coordinate of an integer vector is bounded by its Euclidean norm. -/
private lemma abs_coord_le_eNorm (a : Mon d n → ℤ) (m : Mon d n) : |(a m : ℝ)| ≤ eNorm a := by
  have h1 : ((a m : ℝ)) ^ 2 ≤ ∑ i, ((a i : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg ((a i : ℝ))) (Finset.mem_univ m)
  calc |(a m : ℝ)| = Real.sqrt (((a m : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ i, ((a i : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = eNorm a := rfl

/-- The height ball is contained in the coordinate box of radius `⌈A⌉`. -/
lemma primSet_subset_box (A : ℝ) (P : (Mon d n → ℤ) → Prop) :
    primSet d n A P ⊆ (↑(Fintype.piFinset
      (fun _ : Mon d n => Finset.Icc (-((Nat.ceil A : ℤ))) (Nat.ceil A))) :
        Set (Mon d n → ℤ)) := by
  intro a ha
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro m
  rw [Finset.mem_Icc]
  have h : |(a m : ℤ)| ≤ (Nat.ceil A : ℤ) := by
    have h₁ : |(a m : ℝ)| ≤ (Nat.ceil A : ℝ) :=
      le_trans (abs_coord_le_eNorm a m) (le_trans ha.2.1 (Nat.le_ceil A))
    exact_mod_cast h₁
  exact abs_le.mp h

/-- Height balls are finite. -/
lemma primSet_finite (d n : ℕ) (A : ℝ) (P : (Mon d n → ℤ) → Prop) :
    (primSet d n A P).Finite :=
  (Finset.finite_toSet _).subset (primSet_subset_box A P)

/-- For `k ≥ 4`, `1/k^6` is at most half of the `5`-th power telescoping difference. -/
private lemma telescope_step (k : ℕ) (hk : 4 ≤ k) :
    (1 / (k:ℝ))^6 ≤ (1/2) * ((1 / ((k-1:ℕ):ℝ))^5 - (1 / (k:ℝ))^5) := by
  set u : ℝ := ((k-1:ℕ):ℝ) with hu
  have huk : (k:ℝ) = u + 1 := by
    have h1 : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
    rw [hu, ← h1]; push_cast; ring
  have hu0 : 0 < u := by
    rw [hu]; exact_mod_cast (by omega : 0 < k - 1)
  rw [huk]
  have hden : (0:ℝ) < 2 * u^5 * (u+1)^6 := by positivity
  rw [← sub_nonneg]
  have heq : (1/2) * ((1/u)^5 - (1/(u+1))^5) - (1/(u+1))^6
      = ((u+1)*((u+1)^5 - u^5) - 2*u^5) / (2*u^5*(u+1)^6) := by
    field_simp
  rw [heq]
  apply div_nonneg _ (le_of_lt hden)
  have h : (u+1)*((u+1)^5 - u^5) - 2*u^5 = 3*u^5+15*u^4+20*u^3+15*u^2+6*u+1 := by ring
  rw [h]
  positivity

/-- Tail bound for `Σ 1/k^6` by the `5`-th power telescoping. -/
private lemma sum_inv_pow6_le (B : ℕ) (hB : 5 ≤ B) :
    ∑ k ∈ Finset.Icc 4 B, (1/(k:ℝ))^6 ≤ 1/486 := by
  have hIcc : Finset.Icc 4 B = Finset.Ico 4 (B+1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hB3 : B + 1 - 4 = B - 3 := by omega
  rw [hB3]
  have hstep : ∀ j : ℕ, (1/((4+j:ℕ):ℝ))^6
      ≤ (1/2)*((1/((3+j:ℕ):ℝ))^5 - (1/((4+j:ℕ):ℝ))^5) := by
    intro j
    have h := telescope_step (4+j) (by omega)
    have h1 : (4 + j - 1 : ℕ) = 3 + j := by omega
    simpa [h1] using h
  have hkey : ∑ j ∈ Finset.range (B-3), ((1/((3+j:ℕ):ℝ))^5 - (1/((4+j:ℕ):ℝ))^5)
      = (1/3:ℝ)^5 - (1/(B:ℝ))^5 := by
    have h : ∀ j : ℕ, (1/((4+j:ℕ):ℝ))^5
        = (fun t : ℕ => (1/((3+t:ℕ):ℝ))^5) (j+1) := by
      intro j
      show (1/((4+j:ℕ):ℝ))^5 = (1/((3+(j+1):ℕ):ℝ))^5
      have : (3 + (j+1) : ℕ) = 4 + j := by omega
      rw [this]
    rw [Finset.sum_congr rfl (fun j _ => by rw [h j]), Finset.sum_range_sub']
    have h1 : (3 + (B-3) : ℕ) = B := by omega
    have h2 : (3 + 0 : ℕ) = 3 := by omega
    rw [h1, h2]
    norm_num
  calc ∑ j ∈ Finset.range (B-3), (1/((4+j:ℕ):ℝ))^6
      ≤ ∑ j ∈ Finset.range (B-3), (1/2)*((1/((3+j:ℕ):ℝ))^5 - (1/((4+j:ℕ):ℝ))^5) :=
        Finset.sum_le_sum (fun j _ => hstep j)
    _ = (1/2) * ∑ j ∈ Finset.range (B-3), ((1/((3+j:ℕ):ℝ))^5 - (1/((4+j:ℕ):ℝ))^5) := by
        rw [Finset.mul_sum]
    _ = (1/2) * ((1/3:ℝ)^5 - (1/(B:ℝ))^5) := by rw [hkey]
    _ ≤ 1/486 := by
        have hp : (0:ℝ) < (1/(B:ℝ))^5 := by
          have : (0:ℝ) < (B:ℝ) := by exact_mod_cast (by omega : 0 < B)
          positivity
        have h3 : ((1:ℝ)/3)^5 = 1/243 := by norm_num
        rw [h3]; linarith

/-- The final numeric inequality for the box union bound. -/
private lemma numeric_final (N : ℕ) (hN : 6 ≤ N) (x : ℝ) (hx : 0 < x) :
    3^N * x^N * ((1/2:ℝ)^(N-6) * (1/64+1/729+1/486)) ≤ 2^N * x^N / 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, N = 6 + k := ⟨N - 6, by omega⟩
  rw [show 6 + k - 6 = k by omega]
  have h4 : ((3:ℝ)/2)^k = ((3:ℝ)/4)^k * 2^k := by
    rw [div_pow, div_pow, show (4:ℝ)^k = 2^k * 2^k by rw [← mul_pow]; norm_num]
    field_simp
  have hkey : (729:ℝ) * (1/64+1/729+1/486) * ((3:ℝ)/2)^k ≤ 16 * 2^k := by
    rw [h4]
    have h1 : (729:ℝ) * (1/64+1/729+1/486) ≤ 16 := by norm_num
    have h2 : ((3:ℝ)/4)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc 729 * (1/64+1/729+1/486) * (((3:ℝ)/4)^k * 2^k)
        = (729 * (1/64+1/729+1/486) * ((3:ℝ)/4)^k) * 2^k := by ring
      _ ≤ (16 * 1) * 2^k := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc 729 * (1/64+1/729+1/486) * ((3:ℝ)/4)^k ≤ 16 * ((3:ℝ)/4)^k :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ ≤ 16 * 1 := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 16 * 2^k := by ring
  calc 3^(6+k) * x^(6+k) * ((1/2:ℝ)^k * (1/64+1/729+1/486))
      = (729 * (1/64+1/729+1/486) * ((3:ℝ)/2)^k) * x^(6+k) := by
        have h3 : (3:ℝ)^(6+k) = 729 * 3^k := by rw [pow_add]; norm_num
        have h2 : ((1:ℝ)/2)^k = 1/2^k := by rw [div_pow, one_pow]
        have h5 : ((3:ℝ)/2)^k = 3^k/2^k := by rw [div_pow]
        rw [h3, h2, h5]
        field_simp
    _ ≤ (16 * 2^k) * x^(6+k) := mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = 2^(6+k) * x^(6+k) / 4 := by
        rw [show (2:ℝ)^(6+k) = 64 * 2^k by rw [pow_add]; norm_num]
        ring



/-- Union-bound lower bound for the primitive vectors of a box: the sum of the `g`-divisible
terms is at most a quarter of the leading term `(2B)^N`. -/
private lemma sum_div_bound_aux (N B : ℕ) (hN : 6 ≤ N) (hB : 5 ≤ B) :
    (∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ N) ≤ (2 * (B : ℝ)) ^ N / 4 := by
  have hBpos : (0:ℝ) < (B:ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hterm : ∀ g ∈ Finset.Icc 2 B,
      (2 * ((B / g : ℕ) : ℝ) + 1) ^ N ≤ (3 * (B:ℝ) / g) ^ N := by
    intro g hg
    obtain ⟨hg2, hgB⟩ := Finset.mem_Icc.mp hg
    have hcast : ((B / g : ℕ) : ℝ) ≤ (B:ℝ)/(g:ℝ) := Nat.cast_div_le
    have hb1 : (1:ℝ) ≤ (B:ℝ)/(g:ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast (by omega : 0 < g))]
      have hBg : (g:ℝ) ≤ (B:ℝ) := by exact_mod_cast hgB
      linarith
    have hle : 2 * ((B / g : ℕ) : ℝ) + 1 ≤ 3 * (B:ℝ) / (g:ℝ) := by
      rw [mul_div_assoc]
      linarith
    exact pow_le_pow_left₀ (by positivity) hle N
  have hsum1 : ∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ N
      ≤ ∑ g ∈ Finset.Icc 2 B, (3 * (B:ℝ) / g) ^ N := Finset.sum_le_sum hterm
  have hsum2 : ∑ g ∈ Finset.Icc 2 B, (3 * (B:ℝ) / g) ^ N
      ≤ (3*(B:ℝ))^N * ((1/2:ℝ)^(N-6) * (1/64+1/729+1/486)) := by
    have hfac : ∑ g ∈ Finset.Icc 2 B, (3 * (B:ℝ) / g) ^ N
        = (3*(B:ℝ))^N * ∑ g ∈ Finset.Icc 2 B, ((1:ℝ)/(g:ℝ))^N := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      rw [div_eq_mul_inv, mul_pow, one_div, inv_pow]
    rw [hfac]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ∑ g ∈ Finset.Icc 2 B, ((1:ℝ)/(g:ℝ))^N
        ≤ ∑ g ∈ Finset.Icc 2 B, (1/2:ℝ)^(N-6) * ((1:ℝ)/(g:ℝ))^6 := by
          apply Finset.sum_le_sum
          intro g hg
          obtain ⟨hg2, hgB⟩ := Finset.mem_Icc.mp hg
          have hgpos : (0:ℝ) < (g:ℝ) := by exact_mod_cast (by omega : 0 < g)
          have hle : ((1:ℝ)/(g:ℝ)) ≤ 1/2 := by
            rw [div_le_iff₀ hgpos]
            have h2g : (2:ℝ) ≤ (g:ℝ) := by exact_mod_cast hg2
            linarith
          have hsplit : ((1:ℝ)/(g:ℝ))^N
              = ((1:ℝ)/(g:ℝ))^6 * ((1:ℝ)/(g:ℝ))^(N-6) := by
            conv_lhs => rw [show N = 6 + (N-6) by omega]
            rw [pow_add]
          rw [hsplit]
          have h1 : ((1:ℝ)/(g:ℝ))^(N-6) ≤ (1/2:ℝ)^(N-6) :=
            pow_le_pow_left₀ (by positivity) hle (N-6)
          calc ((1:ℝ)/(g:ℝ))^6 * ((1:ℝ)/(g:ℝ))^(N-6)
              ≤ ((1:ℝ)/(g:ℝ))^6 * (1/2:ℝ)^(N-6) := mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = (1/2:ℝ)^(N-6) * ((1:ℝ)/(g:ℝ))^6 := by ring
      _ = (1/2:ℝ)^(N-6) * ∑ g ∈ Finset.Icc 2 B, ((1:ℝ)/(g:ℝ))^6 := by rw [Finset.mul_sum]
      _ ≤ (1/2:ℝ)^(N-6) * (1/64+1/729+1/486) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hsub : Finset.Icc 2 B ⊆ insert 2 (insert 3 (Finset.Icc 4 B)) := by
            intro g hg
            simp only [Finset.mem_Icc] at hg
            simp only [Finset.mem_insert, Finset.mem_Icc]
            omega
          have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
            (f := fun g : ℕ => ((1:ℝ)/(g:ℝ))^6) (by intro g _ _; positivity)
          have heval : ∑ g ∈ insert 2 (insert 3 (Finset.Icc 4 B)), ((1:ℝ)/(g:ℝ))^6
              = 1/64 + 1/729 + ∑ g ∈ Finset.Icc 4 B, ((1:ℝ)/(g:ℝ))^6 := by
            rw [Finset.sum_insert (by simp [Finset.mem_Icc] :
                  (2:ℕ) ∉ insert 3 (Finset.Icc 4 B)),
                Finset.sum_insert (by simp [Finset.mem_Icc] : (3:ℕ) ∉ Finset.Icc 4 B)]
            norm_num
            ring
          rw [heval] at h
          have htail := sum_inv_pow6_le B hB
          linarith
  have hfin := numeric_final N hN (B:ℝ) hBpos
  have h3 : (3*(B:ℝ))^N = 3^N * (B:ℝ)^N := by rw [mul_pow]
  have h2 : (2*(B:ℝ))^N / 4 = 2^N * (B:ℝ)^N / 4 := by rw [mul_pow]
  rw [h3] at hsum2
  linarith [hsum1, hsum2, hfin, h2]


/-- N01. Height balls are finite and contain `≫ A^N` primitive vectors. -/
theorem count_basic (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    (∀ (A : ℝ) (P : (Mon d n → ℤ) → Prop), (primSet d n A P).Finite) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ A in atTop, c * A ^ NN d n ≤ primCount d n A (fun _ => True) := by
  classical
  have hN6 : 6 ≤ NN d n := six_le_NN d n hd hdn
  have hNpos : (0:ℝ) < (NN d n : ℝ) := by exact_mod_cast (by omega : 0 < NN d n)
  have hs : 0 < Real.sqrt (NN d n : ℝ) := Real.sqrt_pos.mpr hNpos
  refine ⟨fun A P => primSet_finite d n A P,
    1 / (2 * Real.sqrt (NN d n : ℝ) ^ NN d n), ?_, ?_⟩
  · exact div_pos one_pos (mul_pos two_pos (pow_pos hs _))
  · filter_upwards [eventually_ge_atTop (5 * Real.sqrt (NN d n : ℝ))] with A hA
    set B : ℕ := ⌊A / Real.sqrt (NN d n : ℝ)⌋₊ with hB
    have hAs : (0:ℝ) ≤ A := le_trans (by positivity) hA
    have hdiv_nonneg : 0 ≤ A / Real.sqrt (NN d n : ℝ) := div_nonneg hAs (le_of_lt hs)
    have hBle : (B : ℝ) ≤ A / Real.sqrt (NN d n : ℝ) := by
      rw [hB]; exact Nat.floor_le hdiv_nonneg
    have hBlt : A / Real.sqrt (NN d n : ℝ) < (B:ℝ) + 1 := by
      rw [hB]; exact Nat.lt_floor_add_one _
    have hB5 : 5 ≤ B := by
      have h5 : (5:ℝ) ≤ A / Real.sqrt (NN d n : ℝ) := by
        rw [le_div_iff₀ hs]; linarith [hA]
      exact Nat.le_floor h5
    -- Step 1: the primitive vectors of the box lie in the height ball.
    have hcount1 : (((Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
        (fun a => Finset.univ.gcd a = 1)).card : ℝ) ≤ primCount d n A (fun _ => True) := by
      have hsub : ((Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
          (fun a => Finset.univ.gcd a = 1) : Set (Mon d n → ℤ)) ⊆
            primSet d n A (fun _ => True) := by
        intro a ha
        rw [Finset.mem_coe, Finset.mem_filter] at ha
        obtain ⟨hain, hprim⟩ := ha
        rw [Fintype.mem_piFinset] at hain
        refine ⟨hprim, ?_, trivial⟩
        have hcoord : ∀ m, |(a m : ℝ)| ≤ (B : ℝ) := by
          intro m
          have h' : (|a m| : ℤ) ≤ (B : ℤ) := abs_le.mpr (Finset.mem_Icc.mp (hain m))
          exact_mod_cast h'
        have hsq : ∑ m, ((a m : ℝ))^2 ≤ (NN d n : ℝ) * (B:ℝ)^2 := by
          calc ∑ m, ((a m : ℝ))^2 ≤ ∑ m, (B:ℝ)^2 :=
                Finset.sum_le_sum (fun m _ => by rw [sq_le_sq]; simpa using hcoord m)
            _ = (NN d n : ℝ) * (B:ℝ)^2 := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        calc eNorm a = Real.sqrt (∑ m, ((a m : ℝ))^2) := rfl
          _ ≤ Real.sqrt ((NN d n : ℝ) * (B:ℝ)^2) := Real.sqrt_le_sqrt hsq
          _ = Real.sqrt (NN d n : ℝ) * B := by
                rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
          _ ≤ A := by
                have h := hBle
                rw [le_div_iff₀ hs] at h
                linarith
      have h := Set.ncard_le_ncard hsub (primSet_finite d n A (fun _ => True))
      simp only [Set.ncard_coe_finset] at h
      have hh : (((Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
          (fun a => Finset.univ.gcd a = 1)).card : ℝ) ≤
            ((primSet d n A (fun _ => True)).ncard : ℝ) := by
        exact_mod_cast h
      simpa only [primCount] using hh
    -- Step 2: the box lower bound.
    have hcard : ((Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(B : ℤ)) (B : ℤ))).card : ℝ)
        = (2 * (B:ℝ) + 1) ^ (NN d n) := (box_card (ι := Mon d n) B).1
    have hlow : ((Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(B : ℤ)) (B : ℤ))).card : ℝ)
        - 1 - ∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ (NN d n)
        ≤ (((Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
            (fun a => Finset.univ.gcd a = 1)).card : ℝ) := prim_box_lower (ι := Mon d n) B
    have hsumB : (∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ (NN d n))
        ≤ (2 * (B : ℝ)) ^ (NN d n) / 4 := sum_div_bound_aux (NN d n) B hN6 hB5
    have hPB : (1/2) * (2*(B:ℝ)) ^ (NN d n) ≤
        (((Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
          (fun a => Finset.univ.gcd a = 1)).card : ℝ) := by
      rw [hcard] at hlow
      have hB10 : (10:ℝ) ≤ 2*(B:ℝ) := by
        have : (5:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB5
        linarith
      have hx4 : (4:ℝ) ≤ (2*(B:ℝ)) ^ (NN d n) := by
        have h1 : (10:ℝ)^6 ≤ (2*(B:ℝ))^6 := pow_le_pow_left₀ (by norm_num) hB10 6
        have h2 : (2*(B:ℝ))^6 ≤ (2*(B:ℝ))^(NN d n) :=
          pow_le_pow_right₀ (by linarith) hN6
        linarith [h1, h2]
      have hmono : (2*(B:ℝ)) ^ (NN d n) ≤ (2*(B:ℝ)+1) ^ (NN d n) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      linarith [hlow, hsumB, hx4, hmono]
    -- Step 3: conclude with `c = 1/(2 (√N)^N)`.
    have hB2 : A / Real.sqrt (NN d n : ℝ) ≤ 2*(B:ℝ) := by
      have h2 : (2:ℝ) ≤ A / Real.sqrt (NN d n : ℝ) := by
        rw [le_div_iff₀ hs]; linarith [hA]
      linarith [hBlt, hB5, h2]
    have hstep : 1 / (2 * Real.sqrt (NN d n : ℝ) ^ NN d n) * A ^ (NN d n) ≤
        (1/2) * (2*(B:ℝ)) ^ (NN d n) := by
      have h0 : (0:ℝ) ≤ A / Real.sqrt (NN d n : ℝ) := div_nonneg hAs (le_of_lt hs)
      have hpow := pow_le_pow_left₀ h0 hB2 (NN d n)
      have heq : 1 / (2 * Real.sqrt (NN d n : ℝ) ^ NN d n) * A ^ (NN d n)
          = (1/2) * (A / Real.sqrt (NN d n : ℝ)) ^ (NN d n) := by
        rw [div_pow]
        field_simp
      rw [heq]
      linarith [hpow]
    exact le_trans hstep (le_trans hPB hcount1)

end Work.HP
