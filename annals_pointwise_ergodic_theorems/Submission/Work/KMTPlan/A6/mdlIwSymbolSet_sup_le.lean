import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs

namespace Work.KMTPlan.A6

open scoped BigOperators

/-- **A finite set of reals in an interval with pairwise separated points is small.**
If `T ⊆ [a,b]` and any two distinct points of `T` are at distance at least `δ > 0`, then
`#T ≤ (b-a)/δ + 1`. -/
private lemma sep_card_le {T : Finset ℝ} {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    (hsub : ∀ x ∈ T, a ≤ x ∧ x ≤ b)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ |x - y|) :
    (T.card : ℝ) ≤ (b - a) / δ + 1 := by
  have hinj : Set.InjOn (fun x : ℝ => ⌊(x - a) / δ⌋) (T : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have hEq : ((⌊(x - a) / δ⌋ : ℤ) : ℝ) = ⌊(y - a) / δ⌋ := by exact_mod_cast hxy
    have hu : ((⌊(x - a) / δ⌋ : ℤ) : ℝ) ≤ (x - a) / δ := Int.floor_le _
    have hv : ((⌊(y - a) / δ⌋ : ℤ) : ℝ) ≤ (y - a) / δ := Int.floor_le _
    have hu' : (x - a) / δ < ((⌊(x - a) / δ⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hv' : (y - a) / δ < ((⌊(y - a) / δ⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hlt : |(x - a) / δ - (y - a) / δ| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have hxy' : (x - a) / δ - (y - a) / δ = (x - y) / δ := by ring
    rw [hxy', abs_div, abs_of_pos hδ] at hlt
    have h2 : |x - y| < δ := by
      rw [div_lt_one hδ] at hlt
      exact hlt
    linarith [hsep x hx y hy hne]
  have hcard : T.card = (T.image (fun x : ℝ => ⌊(x - a) / δ⌋)).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hsub' : T.image (fun x : ℝ => ⌊(x - a) / δ⌋) ⊆ Finset.Icc (0 : ℤ) ⌊(b - a) / δ⌋ := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.mem_Icc]
    constructor
    · exact Int.floor_nonneg.mpr (div_nonneg (by linarith [(hsub x hx).1]) (le_of_lt hδ))
    · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith [(hsub x hx).2]) (le_of_lt hδ))
  have hnn : (0 : ℤ) ≤ ⌊(b - a) / δ⌋ :=
    Int.floor_nonneg.mpr (div_nonneg (by linarith) (le_of_lt hδ))
  calc (T.card : ℝ) = ((T.image (fun x : ℝ => ⌊(x - a) / δ⌋)).card : ℝ) := by rw [hcard]
    _ ≤ ((Finset.Icc (0 : ℤ) ⌊(b - a) / δ⌋).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub'
    _ = (((⌊(b - a) / δ⌋ + 1 - 0).toNat : ℕ) : ℝ) := by rw [Int.card_Icc]
    _ ≤ (b - a) / δ + 1 := by
        have h1 : (⌊(b - a) / δ⌋ + 1 - 0).toNat ≤ (⌊(b - a) / δ⌋).toNat + 1 := by
          rw [Int.toNat_le]
          have hthis : ((⌊(b - a) / δ⌋).toNat : ℤ) = ⌊(b - a) / δ⌋ := Int.toNat_of_nonneg hnn
          push_cast
          rw [hthis]
          omega
        calc (((⌊(b - a) / δ⌋ + 1 - 0).toNat : ℕ) : ℝ)
            ≤ (((⌊(b - a) / δ⌋).toNat + 1 : ℕ) : ℝ) := by exact_mod_cast h1
          _ = ((⌊(b - a) / δ⌋ : ℤ) : ℝ) + 1 := by
              rw [Nat.cast_add, Nat.cast_one]
              have h2 : ((⌊(b - a) / δ⌋).toNat : ℝ) = ((⌊(b - a) / δ⌋ : ℤ) : ℝ) := by
                exact_mod_cast (Int.toNat_of_nonneg hnn :
                  ((⌊(b - a) / δ⌋).toNat : ℤ) = ⌊(b - a) / δ⌋)
              rw [h2]
          _ ≤ (b - a) / δ + 1 := by linarith [Int.floor_le ((b - a) / δ)]

/-- **Separation of two rational frequencies of bounded denominator.**  If `a/q` and `a'/q'`
are distinct rationals in `[0,1)` with `q, q' ≥ 1`, and `s, t` are reals whose difference `s - t`
differs from `a'/q' - a/q` by an integer and satisfies `|s - t| < 1`, then
`s - t` is at least `1/(q q')` in absolute value. -/
private lemma rat_sep {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    {a a' : ℕ} (ha : a < q) (ha' : a' < q') {s t : ℝ} (hst : |s - t| < 1)
    (hk : ∃ m : ℤ, s - t - ((a' : ℝ) / (q' : ℝ) - (a : ℝ) / (q : ℝ)) = m)
    (hne : (a : ℝ) / (q : ℝ) ≠ (a' : ℝ) / (q' : ℝ)) :
    (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) ≤ |s - t| := by
  obtain ⟨m, hm⟩ := hk
  set w : ℝ := (a' : ℝ) / (q' : ℝ) - (a : ℝ) / (q : ℝ) with hw
  have hm' : s - t - w = (m : ℝ) := by simpa [hw] using hm
  have hqq : (0 : ℝ) < (q : ℝ) * (q' : ℝ) := by positivity
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hq'0 : (q' : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq')
  set K : ℤ := (a' : ℤ) * (q : ℤ) - (a : ℤ) * (q' : ℤ) with hK
  have hweq : w = (K : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
    rw [eq_div_iff (ne_of_gt hqq), hw, hK]
    push_cast
    field_simp
  have hKne : K ≠ 0 := by
    intro hzero
    apply hne
    have hw0 : w = 0 := by rw [hweq, hzero]; simp
    rw [hw] at hw0
    linarith
  have hKlt : K < (q : ℤ) * (q' : ℤ) := by
    have h1 : (a' : ℤ) * (q : ℤ) ≤ ((q' : ℤ) - 1) * (q : ℤ) :=
      mul_le_mul_of_nonneg_right (by omega) (by omega)
    have h2 : ((q' : ℤ) - 1) * (q : ℤ) = (q : ℤ) * (q' : ℤ) - (q : ℤ) := by ring
    have h3 : (0 : ℤ) ≤ (a : ℤ) * (q' : ℤ) := by positivity
    rw [hK]
    omega
  have hKgt : -((q : ℤ) * (q' : ℤ)) < K := by
    have h1 : (a : ℤ) * (q' : ℤ) ≤ ((q : ℤ) - 1) * (q' : ℤ) :=
      mul_le_mul_of_nonneg_right (by omega) (by omega)
    have h2 : ((q : ℤ) - 1) * (q' : ℤ) = (q : ℤ) * (q' : ℤ) - (q' : ℤ) := by ring
    have h3 : (0 : ℤ) ≤ (a' : ℤ) * (q : ℤ) := by positivity
    rw [hK]
    omega
  have hKle : |K| ≤ (q : ℤ) * (q' : ℤ) - 1 := by
    rw [abs_le]
    constructor <;> omega
  have hKabs : (1 : ℝ) ≤ ((|K| : ℤ) : ℝ) := by
    have h1 : (1 : ℤ) ≤ |K| := Int.one_le_abs hKne
    exact_mod_cast h1
  have hcast : ((|K| : ℤ) : ℝ) = |(K : ℝ)| := Int.cast_abs
  have hwpos : (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) ≤ |w| := by
    rw [hweq, abs_div, abs_of_pos hqq]
    rw [le_div_iff₀ hqq]
    rw [hcast] at hKabs
    rw [div_mul_cancel₀ 1 (ne_of_gt hqq)]
    exact hKabs
  have hwle : |w| ≤ 1 - 1 / ((q : ℝ) * (q' : ℝ)) := by
    rw [hweq, abs_div, abs_of_pos hqq]
    have hKleR : ((|K| : ℤ) : ℝ) ≤ ((q : ℤ) * (q' : ℤ) - 1 : ℤ) := by exact_mod_cast hKle
    rw [hcast] at hKleR
    push_cast at hKleR
    rw [div_le_iff₀ hqq]
    have hval : (1 - 1 / ((q : ℝ) * (q' : ℝ))) * ((q : ℝ) * (q' : ℝ))
        = (q : ℝ) * (q' : ℝ) - 1 := by
      rw [sub_mul, one_mul, div_mul_cancel₀ 1 (ne_of_gt hqq)]
    rw [hval]
    exact hKleR
  have hw1 : |w| < 1 := by
    have hpos : (0 : ℝ) < 1 / ((q : ℝ) * (q' : ℝ)) := one_div_pos.mpr hqq
    linarith
  have hm2 : |(m : ℝ)| < 2 := by
    have h4 : (m : ℝ) = s - t - w := by linarith
    rw [h4]
    calc |(s - t) - w| ≤ |s - t| + |w| := abs_sub _ _
      _ < 1 + 1 := by linarith
      _ = 2 := by norm_num
  have hmabs : (-2 : ℤ) < m ∧ m < 2 := by
    have hh := abs_lt.mp hm2
    exact ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2⟩
  obtain ⟨hm_low, hm_high⟩ := hmabs
  have hgen : ∀ mm : ℤ, |(mm : ℝ)| = 1 → 1 - |w| ≤ |w + (mm : ℝ)| := by
    intro mm hmm
    have haux : |(w + (mm : ℝ)) - w| ≤ |w + (mm : ℝ)| + |w| := abs_sub _ _
    rw [add_sub_cancel_left] at haux
    linarith
  have hst_eq : s - t = w + (m : ℝ) := by linarith
  have key : (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) ≤ |w + (m : ℝ)| := by
    interval_cases m
    · exact le_trans (by linarith [hwle]) (hgen (-1) (by norm_num))
    · simpa using hwpos
    · exact le_trans (by linarith [hwle]) (hgen 1 (by norm_num))
  rwa [hst_eq]

/-- **The sup norm of the Ionescu--Wainger symbol over the arithmetic frequency set
`(ℚ/ℤ)_{≤l}`, for a symbol obtained by periodising a function supported in a narrow arc.**

If `ψ` is supported in `[-2^k, 2^k]` with `2^k < 1/2` and `‖ψ‖ ≤ M`, then the periodised symbol
`Φ = periodize ψ` is supported in the arc `ℝ_{≤k}`, so at a frequency `θ` only the arithmetic
frequencies `a/q`, `q ≤ Q`, that lie within `2^k` of `θ` can contribute to
`iwSymbolSet (iwArithFreqs ρ l) Φ θ = ∑_{a/q} Φ (θ - a/q)`.  Distinct such frequencies differ by
at least `1/q q' ≥ 1/Q²`, and they all lie in an arc of length `2·2^k`; hence there are at most
`1 + 2·2^k·Q²` of them, and the symbol is bounded by `(1 + 2·2^k·Q²) M`. -/
theorem mdlIwSymbolSet_sup_le (ρ : ℝ) (l : ℕ) (k : ℤ) (hk : (2 : ℝ) ^ k < 1 / 2)
    (Q : ℕ) (hQ : ∀ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, q ≤ Q)
    (M : ℝ) (hM : 0 ≤ M)
    (ψ : ℝ → ℂ) (hψm : Measurable ψ)
    (hψsupp : ∀ ξ : ℝ, ψ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ k)
    (hψbd : ∀ ξ : ℝ, ‖ψ ξ‖ ≤ M) :
    ∀ θ : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize ψ) θ‖
        ≤ (1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2) * M := by
  -- measurability of `ψ` is not needed for this pointwise bound
  have _hψm : Measurable ψ := hψm
  set ε : ℝ := (2 : ℝ) ^ k with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact zpow_pos (by norm_num) k
  have h2ε : 2 * ε < 1 := by rw [hεdef]; linarith
  -- ## Step 1: the periodised symbol is bounded by `M` pointwise.
  have harc : ∀ x : ℝ, ψ x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k := by
    intro x hx
    rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
    exact abs_le.mp (hψsupp x hx)
  have hΦbd : ∀ η : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.periodize ψ η‖ ≤ M := by
    have h2 : (2 : ℝ) ^ (k + 1) < 1 := by
      rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      linarith
    exact Work.Analysis.IWMultiplier.periodize_norm_le h2 harc hψbd
  -- ## Step 2: the periodised symbol is supported in the arc `ℝ_{≤k}`.
  have hsupparc : Work.Analysis.IonescuWainger.SupportedInArc k
      (Work.Analysis.IonescuWainger.periodize ψ) := by
    intro η hη
    by_contra hcon
    push Not at hcon
    refine hη ?_
    unfold Work.Analysis.IonescuWainger.periodize
    have hzero : (fun j : ℤ => ψ ((AddCircle.equivIco (1 : ℝ) 0 η).val + j)) = fun _ => 0 := by
      funext j
      by_contra hj
      refine (hcon ((AddCircle.equivIco (1 : ℝ) 0 η).val + j) (harc _ hj)) ?_
      rw [AddCircle.coe_add]
      have hjc : (((j : ℤ) : ℝ) : Work.Analysis.IonescuWainger.Circle) = 0 := by
        rw [AddCircle.coe_eq_zero_iff]
        exact ⟨j, by simp⟩
      have hxc : (((AddCircle.equivIco (1 : ℝ) 0 η).val : ℝ) :
          Work.Analysis.IonescuWainger.Circle) = η := AddCircle.coe_equivIco
      rw [hjc, add_zero, hxc]
    rw [hzero, tsum_zero]
  intro θ
  set A : Finset Work.Analysis.IonescuWainger.Circle :=
    Work.Analysis.IonescuWainger.iwArithFreqs ρ l with hAdef
  set S : Finset Work.Analysis.IonescuWainger.Circle :=
    A.filter (fun α => Work.Analysis.IonescuWainger.periodize ψ (θ - α) ≠ 0) with hSdef
  have hAmem : ∀ α, α ∈ A ↔ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l := by
    intro α; rw [hAdef]
  have hSmem : ∀ α, α ∈ S ↔ α ∈ A ∧
      Work.Analysis.IonescuWainger.periodize ψ (θ - α) ≠ 0 := by
    intro α; rw [hSdef]; exact Finset.mem_filter
  have hsym : Work.Analysis.IonescuWainger.iwSymbolSet A
      (Work.Analysis.IonescuWainger.periodize ψ) θ
      = ∑ α ∈ S, Work.Analysis.IonescuWainger.periodize ψ (θ - α) := by
    rw [Work.Analysis.IonescuWainger.iwSymbolSet_apply, hSdef]
    exact (Finset.sum_filter_of_ne (fun α _ hα => hα)).symm
  have hbound : ‖∑ α ∈ S, Work.Analysis.IonescuWainger.periodize ψ (θ - α)‖
      ≤ (S.card : ℝ) * M := by
    calc ‖∑ α ∈ S, Work.Analysis.IonescuWainger.periodize ψ (θ - α)‖
        ≤ ∑ α ∈ S, ‖Work.Analysis.IonescuWainger.periodize ψ (θ - α)‖ := norm_sum_le _ _
      _ ≤ ∑ _α ∈ S, M := Finset.sum_le_sum (fun α _ => hΦbd _)
      _ = (S.card : ℝ) * M := by simp [Finset.sum_const, nsmul_eq_mul]
  -- ## Step 3: at most `1 + 2 ε Q²` of the frequencies contribute.
  have hcard : (S.card : ℝ) ≤ 1 + 2 * ε * (Q : ℝ) ^ 2 := by
    classical
    let f : Work.Analysis.IonescuWainger.Circle → ℝ := fun α =>
      if h : ∃ s : ℝ, |s| ≤ ε ∧ (s : Work.Analysis.IonescuWainger.Circle) = θ - α then
        Classical.choose h else 0
    have hf : ∀ α ∈ S, |f α| ≤ ε ∧
        (f α : Work.Analysis.IonescuWainger.Circle) = θ - α := by
      intro α hα
      have hne : Work.Analysis.IonescuWainger.periodize ψ (θ - α) ≠ 0 := ((hSmem α).mp hα).2
      obtain ⟨s, hsarc, hseq⟩ := hsupparc (θ - α) hne
      rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at hsarc
      rw [← hεdef] at hsarc
      have hsabs : |s| ≤ ε := abs_le.mpr ⟨hsarc.1, hsarc.2⟩
      have hex : ∃ s : ℝ, |s| ≤ ε ∧
          (s : Work.Analysis.IonescuWainger.Circle) = θ - α := ⟨s, hsabs, hseq⟩
      have hspec := Classical.choose_spec hex
      simp only [f, dif_pos hex]
      exact hspec
    have hfinj : Set.InjOn f (S : Set Work.Analysis.IonescuWainger.Circle) := by
      intro α hα β hβ heq
      have h1 := (hf α hα).2
      have h2 := (hf β hβ).2
      have h3 : θ - α = θ - β := by rw [← h1, ← h2, heq]
      exact sub_right_inj.mp h3
    rcases S.eq_empty_or_nonempty with hS0 | ⟨α₀, hα₀⟩
    · rw [hS0, Finset.card_empty, Nat.cast_zero]
      have h1 : (0 : ℝ) ≤ 2 * ε * (Q : ℝ) ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hεpos)) (sq_nonneg _)
      linarith
    · have hQ1 : 1 ≤ Q := by
        have hαA : α₀ ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l :=
          (hAmem α₀).mp ((hSmem α₀).mp hα₀).1
        obtain ⟨q, hqP, hqim⟩ := Finset.mem_biUnion.mp hαA
        obtain ⟨a, hamem, -⟩ := Finset.mem_image.mp hqim
        exact le_trans (Nat.lt_of_le_of_lt (Nat.zero_le a) (Finset.mem_range.mp hamem))
          (hQ q hqP)
      have hQpos : (0 : ℝ) < (Q : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ1)
      have hδpos : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := div_pos one_pos (pow_pos hQpos 2)
      have hTsub : ∀ x ∈ S.image f, -ε ≤ x ∧ x ≤ ε := by
        intro x hx
        obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hx
        have h1 := (hf α hα).1
        rwa [abs_le] at h1
      have hTsep : ∀ x ∈ S.image f, ∀ y ∈ S.image f, x ≠ y →
          (1 : ℝ) / (Q : ℝ) ^ 2 ≤ |x - y| := by
        intro x hx y hy hxy
        obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hy
        have hαβ : α ≠ β := fun h => hxy (by rw [h])
        have hαA : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l :=
          (hAmem α).mp ((hSmem α).mp hα).1
        have hβA : β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l :=
          (hAmem β).mp ((hSmem β).mp hβ).1
        obtain ⟨q, hqP, hqim⟩ := Finset.mem_biUnion.mp hαA
        obtain ⟨a, hamem, haeq⟩ := Finset.mem_image.mp hqim
        obtain ⟨q', hq'P, hq'im⟩ := Finset.mem_biUnion.mp hβA
        obtain ⟨a', ha'mem, ha'eq⟩ := Finset.mem_image.mp hq'im
        have ha_lt : a < q := Finset.mem_range.mp hamem
        have ha'_lt : a' < q' := Finset.mem_range.mp ha'mem
        have hq1 : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le a) ha_lt
        have hq'1 : 0 < q' := Nat.lt_of_le_of_lt (Nat.zero_le a') ha'_lt
        have hqQ : q ≤ Q := hQ q hqP
        have hq'Q : q' ≤ Q := hQ q' hq'P
        have hα1 : (f α : Work.Analysis.IonescuWainger.Circle) = θ - α := (hf α hα).2
        have hβ1 : (f β : Work.Analysis.IonescuWainger.Circle) = θ - β := (hf β hβ).2
        -- the circle relation `(f α - f β) - (a'/q' - a/q) ∈ ℤ`
        have hwrel : ((((a' : ℝ) / (q' : ℝ) - (a : ℝ) / (q : ℝ)) : ℝ) :
            Work.Analysis.IonescuWainger.Circle) = β - α := by
          rw [AddCircle.coe_sub, ha'eq, haeq]
        have hrel : (((f α - f β : ℝ)) : Work.Analysis.IonescuWainger.Circle) = β - α := by
          rw [AddCircle.coe_sub, hα1, hβ1]
          abel
        have hzero : ((((f α - f β) - ((a' : ℝ) / (q' : ℝ) - (a : ℝ) / (q : ℝ)) : ℝ)) :
            Work.Analysis.IonescuWainger.Circle) = 0 := by
          rw [AddCircle.coe_sub, hrel, hwrel, sub_self]
        obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
        have hm' : (m : ℝ) = (f α - f β) - ((a' : ℝ) / (q' : ℝ) - (a : ℝ) / (q : ℝ)) := by
          simpa using hm
        have hst : |f α - f β| < 1 := by
          have h1 := (hf α hα).1
          have h2 := (hf β hβ).1
          have h3 : |f α - f β| ≤ |f α| + |f β| := abs_sub _ _
          linarith
        have hwne : (a : ℝ) / (q : ℝ) ≠ (a' : ℝ) / (q' : ℝ) := by
          intro h
          apply hαβ
          rw [← haeq, ← ha'eq, h]
        have hres := rat_sep hq1 hq'1 ha_lt ha'_lt hst ⟨m, hm'.symm⟩ hwne
        calc (1 : ℝ) / (Q : ℝ) ^ 2 ≤ 1 / ((q : ℝ) * (q' : ℝ)) := by
              apply one_div_le_one_div_of_le
              · exact mul_pos (by exact_mod_cast hq1) (by exact_mod_cast hq'1)
              · have h1 : q * q' ≤ Q * Q := Nat.mul_le_mul hqQ hq'Q
                have h2 : ((q * q' : ℕ) : ℝ) ≤ ((Q * Q : ℕ) : ℝ) := by exact_mod_cast h1
                push_cast at h2
                linarith
          _ ≤ |f α - f β| := hres
      have hTcard : (S.image f).card = S.card := Finset.card_image_of_injOn hfinj
      have hmain := sep_card_le (T := S.image f) (a := -ε) (b := ε) (δ := 1 / (Q : ℝ) ^ 2)
        hδpos (by linarith) hTsub hTsep
      rw [hTcard] at hmain
      have hsimp : (ε - -ε) / ((1 : ℝ) / (Q : ℝ) ^ 2) = 2 * ε * (Q : ℝ) ^ 2 := by
        rw [show (1 : ℝ) / (Q : ℝ) ^ 2 = ((Q : ℝ) ^ 2)⁻¹ by rw [one_div], div_inv_eq_mul]
        ring
      rw [hsimp] at hmain
      linarith
  calc ‖Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize ψ) θ‖
      = ‖∑ α ∈ S, Work.Analysis.IonescuWainger.periodize ψ (θ - α)‖ := by rw [hsym]
    _ ≤ (S.card : ℝ) * M := hbound
    _ ≤ (1 + 2 * ε * (Q : ℝ) ^ 2) * M := mul_le_mul_of_nonneg_right hcard hM

end Work.KMTPlan.A6
