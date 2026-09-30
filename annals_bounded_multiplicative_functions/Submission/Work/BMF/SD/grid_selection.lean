import Mathlib
import Submission.Work.BMF.SD.sd3_defs
import Submission.Work.BMF.SD.grid_near
import Submission.Work.BMF.SD.separated_subset

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

open Classical Polynomial Finset Real Complex

/-! ## Grid selection: pigeonhole over the grid, then thinning

We prove `grid_selection`.  The three ingredients are

* `Work.BMF.SD.grid_near` — every point of `[s, s + J g]` is within `g/2` of some grid point
  `s + j g` with `j ≤ J`;
* `threshold_count` (below) — the pigeonhole estimate: if `n j ≤ M` for all `j ≤ J` and
  `C ≤ Σ_{j ≤ J} n j`, then `C ≤ #{j : t ≤ n j} · (M − t) + (J+1) t`;
* `Work.BMF.SD.separated_subset` — a finite set of naturals of cardinality `≥ m K` contains
  `m` elements that are pairwise at distance `≥ K`.

Combining: the positions of the elements of `S` lie on the grid, so `S` is covered by the `J+1`
balls of radius `g/2`, and at least `m · 2(⌈δ/g⌉₊+1)` of those balls contain `t` or more elements
of `S`.  Taking the sub-family of indices `B` that is `(⌈δ/g⌉₊+1)`-separated (which is where the
factor `2` enters) and reading off the corresponding grid points gives `X`. -/

/-- **Pigeonhole estimate for a threshold count.**  Let `n : ℕ → ℕ` be a family of counts indexed
by `j ≤ J` with `n j ≤ M` for all `j ≤ J` and total at least `C`.  Write `A` for the set of indices
with `n j ≥ t`.  Then

`C ≤ #A · (M − t) + (J+1) · t`.

Indeed `C ≤ Σ_{j ≤ J} n j = Σ_{j ∈ A} n j + Σ_{j ∉ A} n j ≤ #A · M + #Aᶜ · t`, and
`#Aᶜ = (J+1) - #A`, so the right-hand side is `#A · (M − t) + (J+1) · t`. -/
lemma threshold_count (n : ℕ → ℕ) (J : ℕ) (M t C : ℝ)
    (hle : ∀ j, j ≤ J → (n j : ℝ) ≤ M)
    (hsum : C ≤ ∑ j ∈ Finset.range (J + 1), (n j : ℝ)) :
    C ≤ ((Finset.range (J + 1)).filter (fun j => t ≤ (n j : ℝ))).card * (M - t) +
      ((J : ℝ) + 1) * t := by
  set A := (Finset.range (J + 1)).filter (fun j => t ≤ (n j : ℝ)) with hA
  set B := (Finset.range (J + 1)).filter (fun j => ¬ (t ≤ (n j : ℝ))) with hB
  have hsplit : ∑ j ∈ A, (n j : ℝ) + ∑ j ∈ B, (n j : ℝ) =
      ∑ j ∈ Finset.range (J + 1), (n j : ℝ) := by
    rw [hA, hB]
    simpa using Finset.sum_filter_add_sum_filter_not (Finset.range (J+1))
      (fun j => t ≤ (n j : ℝ)) (fun j => (n j : ℝ))
  have hmemA : ∀ j ∈ A, j ≤ J := by
    intro j hj
    rw [hA, Finset.mem_filter] at hj
    have := Finset.mem_range.mp hj.1
    omega
  have hsumA : ∑ j ∈ A, (n j : ℝ) ≤ A.card * M := by
    calc ∑ j ∈ A, (n j : ℝ) ≤ ∑ _j ∈ A, M := Finset.sum_le_sum (fun j hj => hle j (hmemA j hj))
      _ = A.card * M := by rw [Finset.sum_const, nsmul_eq_mul]
  have hsumB : ∑ j ∈ B, (n j : ℝ) ≤ B.card * t := by
    calc ∑ j ∈ B, (n j : ℝ) ≤ ∑ _j ∈ B, t := Finset.sum_le_sum (fun j hj => by
          rw [hB, Finset.mem_filter] at hj
          exact le_of_lt (not_le.mp hj.2))
      _ = B.card * t := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcardB : B.card = (J + 1) - A.card := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.range (J+1))
      (p := fun j => t ≤ (n j : ℝ))
    rw [Finset.card_range] at h
    rw [← hA, ← hB] at h
    omega
  have hAle : A.card ≤ J + 1 := by
    rw [hA]
    calc ((Finset.range (J+1)).filter (fun j => t ≤ (n j : ℝ))).card ≤
          (Finset.range (J+1)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = J + 1 := Finset.card_range _
  have hstep : C ≤ A.card * M + B.card * t := by
    have h1 : ∑ j ∈ A, (n j : ℝ) + ∑ j ∈ B, (n j : ℝ) ≤ A.card * M + B.card * t :=
      add_le_add hsumA hsumB
    linarith
  have hgoal : A.card * M + B.card * t = A.card * (M - t) + ((J : ℝ) + 1) * t := by
    rw [hcardB, Nat.cast_sub hAle]
    push_cast
    ring
  linarith

/-- `⌈δ/g⌉₊ · g ≥ δ` whenever `g > 0`. -/
lemma ceil_mul_ge {δ g : ℝ} (hg : 0 < g) :
    δ ≤ (((⌈δ / g⌉₊ + 1 : ℕ)) : ℝ) * g := by
  have h1 : δ / g ≤ ((⌈δ / g⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : δ / g * g = δ := by rw [div_mul_cancel₀ δ (ne_of_gt hg)]
  have h3 := mul_le_mul_of_nonneg_right h1 hg.le
  rw [h2] at h3
  push_cast
  nlinarith [h3, hg]

/-- Two grid points whose indices differ by at least `K` (with `K g ≥ δ`) are `δ`-separated. -/
lemma grid_sep {s g δ : ℝ} {K : ℕ} (hg : 0 < g) (hKg : δ ≤ ((K : ℝ)) * g)
    {a b : ℕ} (hab : a < b) (hK : K ≤ b - a) :
    δ ≤ |(s + (a : ℝ) * g) - (s + (b : ℝ) * g)| := by
  have hba : ((K : ℕ) : ℝ) ≤ ((b - a : ℕ) : ℝ) := by exact_mod_cast hK
  have h2 : ((b : ℝ) - (a : ℝ)) = ((b - a : ℕ) : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hab)]
  have h1 : (s + (a : ℝ) * g) - (s + (b : ℝ) * g) = -(((b : ℝ) - (a : ℝ)) * g) := by ring
  rw [h1, h2, abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hg]
  have := mul_le_mul_of_nonneg_right hba hg.le
  linarith

/-- **Grid pigeonhole + thinning.**  Let `S` be a finite set of pairs whose "positions" `q.1/q.2`
all lie in `[s, s + J g]`, and assume that every ball of radius `g/2` contains at most `M` elements
of `S`, and `t + 1 ≤ M`.  If `S.card ≥ m·2(⌈δ/g⌉+1)·(M − t) + (J+1)·t`, then there are `m` grid
points `s + j g` (`j ≤ J`), pairwise `δ`-separated, each of whose balls of radius `g/2` contains at
least `t` elements of `S`.

Proof: every element lies in the ball of its nearest grid point, so `Σ_{j≤J} n_j ≥ S.card` with
`n_j := #(ballPairs S (s + j g) (g/2))`; hence `#{j : n_j ≥ t} ≥ (S.card − (J+1)t)/(M − t)`; then
select every second block of `⌈δ/g⌉ + 1` consecutive indices among the selected ones, and the
selected indices differ by at least `(⌈δ/g⌉+1)·g ≥ δ`. -/
theorem grid_selection (S : Finset (ℝ × ℕ)) (s g M t δ : ℝ) (J m : ℕ)
    (hg : 0 < g) (hJ : 0 < J) (htM : t + 1 ≤ M)
    (hpos : ∀ q ∈ S, s ≤ q.1 / (q.2 : ℝ) ∧ q.1 / (q.2 : ℝ) ≤ s + (J : ℝ) * g)
    (hbound : ∀ x : ℝ, ((Work.BMF.ballPairs S x (g / 2)).card : ℝ) ≤ M)
    (hT : (m : ℝ) * (2 * (⌈δ / g⌉₊ + 1)) * (M - t) + ((J : ℕ) + 1 : ℝ) * t ≤ (S.card : ℝ)) :
    ∃ X : Finset ℝ, (∀ u ∈ X, ∃ j : ℕ, j ≤ J ∧ u = s + (j : ℝ) * g) ∧
      (∀ u ∈ X, ∀ v ∈ X, u ≠ v → δ ≤ |u - v|) ∧
      m ≤ X.card ∧ ∀ u ∈ X, t ≤ ((Work.BMF.ballPairs S u (g / 2)).card : ℝ) := by
  -- the grid and the ball counts along it
  set G : ℕ → ℝ := fun j => s + (j : ℝ) * g with hG
  set n : ℕ → ℕ := fun j => (Work.BMF.ballPairs S (G j) (g / 2)).card with hn
  -- Step 1: every element of `S` lies in the ball of its nearest grid point
  have hcover : S ⊆ (Finset.range (J+1)).biUnion
      (fun j => Work.BMF.ballPairs S (G j) (g / 2)) := by
    intro q hq
    obtain ⟨h1, h2⟩ := hpos q hq
    obtain ⟨j, hjJ, hjabs⟩ := grid_near (q.1 / (q.2 : ℝ)) s g J hg h1 h2
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjJ), ?_⟩
    rw [Work.BMF.mem_ballPairs]
    exact ⟨hq, by simpa only [hG] using hjabs⟩
  -- Step 2: the sum of the ball counts dominates `S.card`
  have hsum : (S.card : ℝ) ≤ ∑ j ∈ Finset.range (J+1), (n j : ℝ) := by
    have h1 : S.card ≤ ((Finset.range (J+1)).biUnion
        (fun j => Work.BMF.ballPairs S (G j) (g / 2))).card := Finset.card_le_card hcover
    have h2 : ((Finset.range (J+1)).biUnion
        (fun j => Work.BMF.ballPairs S (G j) (g / 2))).card ≤
        ∑ j ∈ Finset.range (J+1), (Work.BMF.ballPairs S (G j) (g / 2)).card :=
      Finset.card_biUnion_le
    calc (S.card : ℝ) ≤ (((Finset.range (J+1)).biUnion
          (fun j => Work.BMF.ballPairs S (G j) (g / 2))).card : ℝ) := by exact_mod_cast h1
      _ ≤ ((∑ j ∈ Finset.range (J+1),
            (Work.BMF.ballPairs S (G j) (g / 2)).card : ℕ) : ℝ) := by exact_mod_cast h2
      _ = ∑ j ∈ Finset.range (J+1), (n j : ℝ) := by
            simp only [hn]
            push_cast
            rfl
  -- Step 3: pigeonhole — many grid points carry at least `t` elements
  set A := (Finset.range (J+1)).filter (fun j => t ≤ (n j : ℝ)) with hA
  have hcount : (S.card : ℝ) ≤ (A.card : ℝ) * (M - t) + ((J : ℝ) + 1) * t := by
    have := threshold_count n J M t (S.card) (fun j _ => hbound (G j)) hsum
    rwa [← hA] at this
  have hMt : 0 < M - t := by linarith
  have hkey : (m : ℝ) * (2 * ((⌈δ / g⌉₊ : ℝ) + 1)) ≤ (A.card : ℝ) := by
    have hT' := hT
    have h1 : (m : ℝ) * (2 * ((⌈δ / g⌉₊ : ℝ) + 1)) * (M - t) ≤
        (A.card : ℝ) * (M - t) := by
      linarith [hT', hcount]
    exact le_of_mul_le_mul_right h1 hMt
  -- Step 4: thin out the indices to a `(⌈δ/g⌉₊+1)`-separated sub-family
  have hnat : m * (⌈δ / g⌉₊ + 1) ≤ A.card := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h3 : (((m * (⌈δ / g⌉₊ + 1) : ℕ)) : ℝ) ≤ (A.card : ℝ) := by
      push_cast
      nlinarith [hkey, hm0]
    exact_mod_cast h3
  obtain ⟨B, hBA, hBcard, hBsep⟩ :=
    separated_subset A (⌈δ / g⌉₊ + 1) m (Nat.succ_pos _) hnat
  have hBrange : B ⊆ Finset.range (J+1) := by
    intro j hj
    have hjA := hBA hj
    rw [hA, Finset.mem_filter] at hjA
    exact hjA.1
  -- Step 5: read off the grid points
  refine ⟨B.image G, ?_, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨j, hjB, hju⟩ := Finset.mem_image.mp hu
    have hjJ : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hBrange hjB))
    exact ⟨j, hjJ, by rw [← hju]⟩
  · intro u hu v hv huv
    obtain ⟨a, haB, hau⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hbB, hbv⟩ := Finset.mem_image.mp hv
    simp only [hG] at hau hbv
    rw [← hau, ← hbv]
    have hab : a ≠ b := by
      intro h
      exact huv (by rw [← hau, ← hbv, h])
    rcases lt_or_gt_of_ne hab with hab | hab
    · exact grid_sep hg (ceil_mul_ge hg) hab (hBsep a haB b hbB hab)
    · rw [abs_sub_comm]
      exact grid_sep hg (ceil_mul_ge hg) hab (hBsep b hbB a haB hab)
  · have hinj : Set.InjOn G ↑B := by
      intro a _ b _ hab
      simp only [hG] at hab
      have h1 : (a : ℝ) * g = (b : ℝ) * g := by linarith
      have h2 : (a : ℝ) = (b : ℝ) := mul_right_cancel₀ (ne_of_gt hg) h1
      exact_mod_cast h2
    rw [Finset.card_image_of_injOn hinj, hBcard]
  · intro u hu
    obtain ⟨j, hjB, hju⟩ := Finset.mem_image.mp hu
    have hjA := hBA hjB
    rw [hA, Finset.mem_filter] at hjA
    simp only [hn] at hjA
    rw [← hju]
    exact hjA.2

end Work.BMF.SD
