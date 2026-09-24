import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs

/-!
# GM Lemma 8.2: the `L²` bound for `R`

`Rfun W v = Σ_{t ∈ W} |v|^{it}` and `T = M N = N^{6/5}`.  For every `ε > 0` there is `C > 0` and
`N₀` such that for `N ≥ N₀`, for every `W ⊆ [0, M N]` that is `(M N)^ε`-separated,
`∫_1^2 ‖Rfun W v‖^2 dv ≤ C * N^ε * |W|`.

The proof expands the square, uses `∫_1^2 v^{i(t-t')} dv ≪ 1/(1+|t-t'|)`, so that the diagonal
contributes `|W|` and the off-diagonal contributes `≪ |W| log T / T^ε ≪ |W| N^ε` by separation.
-/

open Finset
open scoped BigOperators

namespace Work.GM.S3

/-- **Counting lemma.** A `δ`-separated finite set of reals contained in `[a,b]` has at most
`(b-a)/δ + 1` elements: the map `w ↦ ⌊(w-a)/δ⌋` is injective on `W`. -/
lemma card_le_of_separated {W : Finset ℝ} {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    (hsub : ∀ w ∈ W, a ≤ w ∧ w ≤ b)
    (hsep : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → δ ≤ |t - s|) :
    (W.card : ℝ) ≤ (b - a) / δ + 1 := by
  set g : ℝ → ℕ := fun w => ⌊(w - a) / δ⌋₊ with hg
  have hinj : Set.InjOn g (W : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have hax : 0 ≤ (x - a) / δ := by have := (hsub x hx).1; positivity
    have hay : 0 ≤ (y - a) / δ := by have := (hsub y hy).1; positivity
    have hx1 : ((g x : ℕ) : ℝ) ≤ (x - a)/δ := Nat.floor_le hax
    have hx2 : (x - a)/δ < ((g x : ℕ) : ℝ) + 1 := ((Nat.floor_eq_iff hax).mp rfl).2
    have hy1 : ((g y : ℕ) : ℝ) ≤ (y - a)/δ := Nat.floor_le hay
    have hy2 : (y - a)/δ < ((g y : ℕ) : ℝ) + 1 := ((Nat.floor_eq_iff hay).mp rfl).2
    rw [hxy] at hx1 hx2
    have h3 : |(x - a)/δ - (y - a)/δ| < 1 := by
      rw [abs_lt]; exact ⟨by linarith, by linarith⟩
    have h4 : |x - y| / δ < 1 := by
      have heq : (x - a)/δ - (y - a)/δ = (x - y)/δ := by ring
      rw [heq, abs_div] at h3
      rwa [abs_of_pos hδ] at h3
    have h5 : |x - y| < δ := by rw [div_lt_one hδ] at h4; exact h4
    linarith [hsep x hx y hy hne]
  have hcard := Finset.card_image_of_injOn hinj
  have hsubimg : W.image g ⊆ Finset.Icc 0 ⌊(b - a) / δ⌋₊ := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [Finset.mem_Icc]
    refine ⟨Nat.zero_le _, Nat.floor_mono ?_⟩
    rw [div_le_div_iff_of_pos_right hδ]
    linarith [(hsub w hw).1, (hsub w hw).2]
  have h2 : ((W.image g).card : ℝ) ≤ (⌊(b - a) / δ⌋₊ : ℝ) + 1 := by
    have h := Finset.card_le_card hsubimg
    rw [Nat.card_Icc, Nat.sub_zero] at h
    exact_mod_cast h
  have h3 : (⌊(b - a) / δ⌋₊ : ℝ) + 1 ≤ (b - a) / δ + 1 := by
    have := Nat.floor_le (show (0:ℝ) ≤ (b - a)/δ by positivity)
    linarith
  calc (W.card : ℝ) = ((W.image g).card : ℝ) := by rw [hcard]
    _ ≤ (⌊(b - a) / δ⌋₊ : ℝ) + 1 := h2
    _ ≤ (b - a) / δ + 1 := h3

/-- **One-sided reciprocal sum.** If `S ⊆ W` consists of points strictly to the right of `t ∈ W`,
`W ⊆ [a,b]` is `δ`-separated, then `Σ_{s ∈ S} (1+|t-s|)^{-1} ≤ δ⁻¹ (1 + log((b-a)/δ + 2))`:
the `k`-th point to the right is at distance at least `kδ`, so the sum is bounded by the harmonic
sum `H_{|S|} ≤ 1 + log|S| ≤ 1 + log((b-a)/δ + 2)`. -/
lemma sum_side_le (W S : Finset ℝ) (δ a b t : ℝ) (hδ : 0 < δ) (hab : a ≤ b)
    (ht : t ∈ W) (hsub : ∀ w ∈ W, w ∈ Set.Icc a b)
    (hSW : S ⊆ W) (hside : ∀ s ∈ S, t < s)
    (hsep : ∀ s ∈ W, ∀ s' ∈ W, s ≠ s' → δ ≤ |s - s'|) :
    (∑ s ∈ S, 1 / (1 + |t - s|)) ≤ (1 / δ) * (1 + Real.log ((b - a) / δ + 2)) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.sum_empty]
    have h1 : (0:ℝ) ≤ (b - a)/δ := by positivity
    have h2 : (0:ℝ) ≤ 1/δ := by positivity
    have h3 : (0:ℝ) ≤ Real.log ((b - a)/δ + 2) := Real.log_nonneg (by linarith)
    have h4 : (0:ℝ) ≤ 1 + Real.log ((b-a)/δ + 2) := by linarith
    exact mul_nonneg h2 h4
  set k : ℝ → ℕ := fun s => (S.filter (fun x => |t - x| ≤ |t - s|)).card with hk
  have hkpos : ∀ s ∈ S, 1 ≤ k s := by
    intro s hs
    rw [hk]
    exact Finset.card_pos.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, le_rfl⟩⟩
  have hkle : ∀ s ∈ S, k s ≤ S.card := by
    intro s hs; rw [hk]; exact Finset.card_filter_le _ _
  have hkmono : ∀ s ∈ S, ∀ s' ∈ S, s < s' → k s < k s' := by
    intro s hs s' hs' hlt
    have hst : |t - s| = s - t := by rw [abs_of_neg (by linarith [hside s hs])]; ring
    have hs't : |t - s'| = s' - t := by rw [abs_of_neg (by linarith [hside s' hs'])]; ring
    have hss : S.filter (fun x => |t - x| ≤ |t - s|) ⊂
        S.filter (fun x => |t - x| ≤ |t - s'|) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, by linarith [hx.2, hst, hs't]⟩
      · intro heq
        have hmem : s' ∈ S.filter (fun x => |t - x| ≤ |t - s|) := by
          rw [heq]
          exact Finset.mem_filter.mpr ⟨hs', by linarith [hst, hs't]⟩
        have h1 : s' - t ≤ s - t := by
          rw [← hs't, ← hst]
          exact (Finset.mem_filter.mp hmem).2
        linarith
    rw [hk]
    exact Finset.card_lt_card hss
  have hkinj : Set.InjOn k (S : Set ℝ) := by
    intro x hx y hy hxy
    rcases lt_trichotomy x y with h | h | h
    · exact absurd hxy (ne_of_lt (hkmono x hx y hy h))
    · exact h
    · exact absurd hxy.symm (ne_of_lt (hkmono y hy x hx h))
  have hAsepinj : ∀ (T : Finset ℝ), T ⊆ W → ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ |x - y| :=
    fun T hT x hx y hy => hsep x (hT hx) y (hT hy)
  have hkey : ∀ s ∈ S, (k s : ℝ) * δ ≤ s - t := by
    intro s hs
    have hts : t < s := hside s hs
    have hnm : t ∉ S.filter (fun x => |t - x| ≤ |t - s|) := by
      intro htmem
      exact absurd (hside t (Finset.mem_filter.mp htmem).1) (lt_irrefl t)
    have hcardA : (insert t (S.filter (fun x => |t - x| ≤ |t - s|))).card = k s + 1 := by
      rw [Finset.card_insert_of_notMem hnm, hk]
    have hmemA : ∀ z ∈ insert t (S.filter (fun x => |t - x| ≤ |t - s|)), z ∈ W := by
      intro z hz
      rcases Finset.mem_insert.mp hz with h | h
      · rw [h]; exact ht
      · exact hSW (Finset.mem_filter.mp h).1
    have hsubA : ∀ w ∈ insert t (S.filter (fun x => |t - x| ≤ |t - s|)),
        t ≤ w ∧ w ≤ s := by
      intro w hw
      rcases Finset.mem_insert.mp hw with h | h
      · rw [h]; exact ⟨le_rfl, le_of_lt hts⟩
      · rw [Finset.mem_filter] at h
        have hwt : t < w := hside w h.1
        refine ⟨le_of_lt hwt, ?_⟩
        have h1 : |t - w| = w - t := by rw [abs_of_neg (by linarith)]; ring
        have h2 : |t - s| = s - t := by rw [abs_of_neg (by linarith)]; ring
        linarith [h.2, h1, h2]
    have hsepB : ∀ x ∈ insert t (S.filter (fun x => |t - x| ≤ |t - s|)),
        ∀ y ∈ insert t (S.filter (fun x => |t - x| ≤ |t - s|)), x ≠ y → δ ≤ |x - y| :=
      fun x hx y hy hxy => hsep x (hmemA x hx) y (hmemA y hy) hxy
    have hcount := card_le_of_separated hδ (le_of_lt hts) hsubA hsepB
    rw [hcardA] at hcount
    have hcount' : (k s : ℝ) ≤ (s - t) / δ := by
      have : ((k s : ℕ) : ℝ) + 1 ≤ (s - t) / δ + 1 := by
        push_cast at hcount ⊢; exact hcount
      linarith
    exact (le_div_iff₀ hδ).mp hcount'
  have hm : (S.card : ℝ) ≤ (b - a) / δ := by
    have hcardA : (S ∪ {t}).card = S.card + 1 := by
      rw [Finset.card_union_of_disjoint]
      · rw [Finset.card_singleton]
      · rw [Finset.disjoint_singleton_right]
        intro hmem
        exact absurd (hside t hmem) (lt_irrefl t)
    have hsubA : ∀ w ∈ S ∪ {t}, a ≤ w ∧ w ≤ b := by
      intro w hw
      rcases Finset.mem_union.mp hw with hw | hw
      · exact ⟨(hsub w (hSW hw)).1, (hsub w (hSW hw)).2⟩
      · rw [Finset.mem_singleton.mp hw]; exact ⟨(hsub t ht).1, (hsub t ht).2⟩
    have hsubW : S ∪ {t} ⊆ W := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hSW hx
      · rw [Finset.mem_singleton.mp hx]; exact ht
    have hcount := card_le_of_separated hδ hab hsubA (hAsepinj _ hsubW)
    rw [hcardA] at hcount
    have : (S.card : ℝ) + 1 ≤ (b - a)/δ + 1 := by push_cast at hcount ⊢; exact hcount
    linarith
  calc (∑ s ∈ S, 1 / (1 + |t - s|))
      ≤ ∑ s ∈ S, 1 / |t - s| := by
        refine Finset.sum_le_sum fun s hs => ?_
        have h : (0:ℝ) < |t - s| := abs_pos.mpr (by linarith [hside s hs])
        exact one_div_le_one_div_of_le h (by linarith)
    _ ≤ ∑ s ∈ S, (1 / δ) * (1 / (k s : ℝ)) := by
        refine Finset.sum_le_sum fun s hs => ?_
        have hk1 : (0:ℝ) < (k s : ℝ) := by exact_mod_cast hkpos s hs
        have h2 : (k s : ℝ) * δ ≤ |t - s| := by
          have habs : |t - s| = s - t := by
            rw [abs_of_neg (by linarith [hside s hs])]; ring
          rw [habs]; exact hkey s hs
        have h3 : (0:ℝ) < (k s : ℝ) * δ := mul_pos hk1 hδ
        calc 1 / |t - s| ≤ 1 / ((k s : ℝ) * δ) := one_div_le_one_div_of_le h3 h2
          _ = (1 / δ) * (1 / (k s : ℝ)) := by field_simp
    _ = (1 / δ) * ∑ s ∈ S, 1 / (k s : ℝ) := by rw [Finset.mul_sum]
    _ = (1 / δ) * ∑ r ∈ S.image k, 1 / (r : ℝ) := by rw [Finset.sum_image hkinj]
    _ ≤ (1 / δ) * ∑ r ∈ Finset.Icc 1 S.card, 1 / (r : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro r hr
            rw [Finset.mem_image] at hr
            obtain ⟨s, hs, rfl⟩ := hr
            rw [Finset.mem_Icc]
            exact ⟨hkpos s hs, hkle s hs⟩
          · intro r hr _
            positivity
    _ = (1 / δ) * ((harmonic S.card : ℚ) : ℝ) := by
          congr 1
          rw [harmonic_eq_sum_Icc, Rat.cast_sum]
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [Rat.cast_inv, Rat.cast_natCast, one_div]
    _ ≤ (1 / δ) * (1 + Real.log ((b - a) / δ + 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (harmonic_le_one_add_log _).trans ?_
          have hlog : Real.log (S.card : ℝ) ≤ Real.log ((b - a)/δ + 2) := by
            apply Real.log_le_log (by positivity)
            linarith [hm]
          linarith

/-- **One-sided reciprocal sum, either side.** As `sum_side_le`, but `S` may lie either to the
right or to the left of `t`; the left case is the right case for the reflected configuration
`x ↦ -x` (all hypotheses and the conclusion are invariant under reflection). -/
lemma sum_side_le' (W S : Finset ℝ) (δ a b t : ℝ) (hδ : 0 < δ) (hab : a ≤ b)
    (ht : t ∈ W) (hsub : ∀ w ∈ W, w ∈ Set.Icc a b)
    (hSW : S ⊆ W) (hside : (∀ s ∈ S, t < s) ∨ (∀ s ∈ S, s < t))
    (hsep : ∀ s ∈ W, ∀ s' ∈ W, s ≠ s' → δ ≤ |s - s'|) :
    (∑ s ∈ S, 1 / (1 + |t - s|)) ≤ (1 / δ) * (1 + Real.log ((b - a) / δ + 2)) := by
  rcases hside with hR | hL
  · exact sum_side_le W S δ a b t hδ hab ht hsub hSW hR hsep
  · set φ : ℝ → ℝ := fun x => -x with hφ
    have hinj : Set.InjOn φ (S : Set ℝ) := by
      intro x _ y _ hxy
      simpa [hφ] using hxy
    have himg : (∑ s ∈ S.image φ, 1 / (1 + |(-t) - s|)) = ∑ s ∈ S, 1 / (1 + |t - s|) := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun s hs => ?_
      simp only [hφ]
      have h1 : (-t) - (-s) = s - t := by ring
      rw [h1, abs_sub_comm]
    have hsub' : ∀ w ∈ W.image φ, w ∈ Set.Icc (-b) (-a) := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨w₀, hw₀, hw⟩
      rw [← hw]
      simp only [hφ]
      have h := hsub w₀ hw₀
      rw [Set.mem_Icc] at h ⊢
      constructor <;> linarith [h.1, h.2]
    have hside' : ∀ s ∈ S.image φ, -t < s := by
      intro s hs
      rcases Finset.mem_image.mp hs with ⟨s₀, hs₀, hs⟩
      rw [← hs]
      simp only [hφ]
      linarith [hL s₀ hs₀]
    have hsep' : ∀ s ∈ W.image φ, ∀ s' ∈ W.image φ, s ≠ s' → δ ≤ |s - s'| := by
      intro s hs s' hs' hsne
      rcases Finset.mem_image.mp hs with ⟨s₀, hs₀, hs⟩
      rcases Finset.mem_image.mp hs' with ⟨s₀', hs₀', hs'⟩
      rw [← hs, ← hs']
      simp only [hφ]
      have hne : s₀ ≠ s₀' := by
        intro h
        exact hsne (by rw [← hs, ← hs', h])
      have hgoal : |-s₀ - -s₀'| = |s₀ - s₀'| := by
        rw [sub_neg_eq_add, show (-s₀) + s₀' = -(s₀ - s₀') by ring, abs_neg]
      rw [hgoal]
      exact hsep s₀ hs₀ s₀' hs₀' hne
    have h := sum_side_le (W.image φ) (S.image φ) δ (-b) (-a) (-t) hδ (by linarith)
      (Finset.mem_image.mpr ⟨t, ht, by simp [hφ]⟩) hsub' (Finset.image_subset_image hSW) hside' hsep'
    have hba : (-a) - (-b) = b - a := by ring
    rw [hba] at h
    rw [himg] at h
    exact h

/-- **The separated reciprocal sum.** If `W ⊆ [0,T]` is `δ`-separated (`δ > 0`) then
`Σ_{t,t' ∈ W} (1+|t-t'|)^{-1} ≤ |W| (1 + 2(1 + log(T/δ+2))/δ)`. -/
theorem sep_recip_sum (W : Finset ℝ) (δ T : ℝ) (hδ : 0 < δ)
    (hsub : ∀ t ∈ W, t ∈ Set.Icc 0 T)
    (hsep : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → δ ≤ |t - s|) :
    (∑ t ∈ W, ∑ t' ∈ W, 1 / (1 + |t - t'|))
      ≤ (W.card : ℝ) * (1 + 2 * (1 + Real.log (T / δ + 2)) / δ) := by
  rcases W.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨t₀, ht₀⟩ := hne
  have hT0 : 0 ≤ T := by
    have h := hsub t₀ ht₀
    rw [Set.mem_Icc] at h
    linarith [h.1, h.2]
  have hbound : ∀ t ∈ W, (∑ t' ∈ W, 1 / (1 + |t - t'|))
      ≤ 1 + 2 * (1 + Real.log (T / δ + 2)) / δ := by
    intro t ht
    set f : ℝ → ℝ := fun t' => 1 / (1 + |t - t'|) with hf
    set SR := W.filter (fun s => t < s) with hSR
    set SL := W.filter (fun s => s < t) with hSL
    have hER : W.erase t = SR ∪ SL := by
      ext x
      simp only [hSR, hSL, Finset.mem_erase, Finset.mem_filter, Finset.mem_union]
      constructor
      · intro hx
        rcases lt_trichotomy x t with h | h | h
        · exact Or.inr ⟨hx.2, h⟩
        · exact absurd h hx.1
        · exact Or.inl ⟨hx.2, h⟩
      · rintro (⟨hxW, h⟩ | ⟨hxW, h⟩)
        · exact ⟨ne_of_gt h, hxW⟩
        · exact ⟨ne_of_lt h, hxW⟩
    have hdisj : Disjoint SR SL := by
      rw [Finset.disjoint_left]
      intro x hxR hxL
      rw [hSR, Finset.mem_filter] at hxR
      rw [hSL, Finset.mem_filter] at hxL
      linarith [hxR.2, hxL.2]
    have hft : f t = 1 := by
      simp [hf]
    have hsum : (∑ t' ∈ W, f t') = (∑ s ∈ SR, f s) + (∑ s ∈ SL, f s) + 1 := by
      rw [← Finset.sum_erase_add W f ht, hER, Finset.sum_union hdisj, hft]
    have hR : (∑ s ∈ SR, f s) ≤ (1 / δ) * (1 + Real.log ((T - 0) / δ + 2)) :=
      sum_side_le' W SR δ 0 T t hδ hT0 ht (fun w hw => hsub w hw) (by rw [hSR]; exact Finset.filter_subset _ _)
        (Or.inl (fun s hs => (Finset.mem_filter.mp hs).2)) hsep
    have hL : (∑ s ∈ SL, f s) ≤ (1 / δ) * (1 + Real.log ((T - 0) / δ + 2)) :=
      sum_side_le' W SL δ 0 T t hδ hT0 ht (fun w hw => hsub w hw) (by rw [hSL]; exact Finset.filter_subset _ _)
        (Or.inr (fun s hs => (Finset.mem_filter.mp hs).2)) hsep
    rw [hsum]
    rw [show (T - 0 : ℝ) = T by ring] at hR hL
    have : ((1 / δ) * (1 + Real.log (T / δ + 2))) * 2 = 2 * (1 + Real.log (T / δ + 2)) / δ := by ring
    linarith [hR, hL, this]
  calc (∑ t ∈ W, ∑ t' ∈ W, 1 / (1 + |t - t'|))
      ≤ ∑ t ∈ W, (1 + 2 * (1 + Real.log (T / δ + 2)) / δ) := Finset.sum_le_sum hbound
    _ = (W.card : ℝ) * (1 + 2 * (1 + Real.log (T / δ + 2)) / δ) := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- **The pair integral.** `‖∫_1^2 v^{iΔ} dv‖ ≤ 6/(1+|Δ|)`. For `Δ ≠ 0` the integrand has the
antiderivative `v^{1+iΔ}/(1+iΔ)`, giving `∫_1^2 v^{iΔ} dv = (2^{1+iΔ}-1)/(1+iΔ)` of modulus at most
`3/√(1+Δ²) ≤ 6/(1+|Δ|)`; for `Δ = 0` the integral is `1 ≤ 6`. -/
theorem pair_integral_bound (Δ : ℝ) :
    ‖∫ v in (1 : ℝ)..2, ((v : ℂ) ^ (Complex.I * (Δ : ℂ)))‖ ≤ 6 / (1 + |Δ|) := by
  by_cases hΔ : Δ = 0
  · subst hΔ
    have hzero : ∀ v : ℝ, ((v:ℂ)^(Complex.I * ((0:ℝ):ℂ))) = 1 := by
      intro v; rw [Complex.ofReal_zero, mul_zero, Complex.cpow_zero]
    rw [intervalIntegral.integral_congr (fun v _ => hzero v)]
    rw [intervalIntegral.integral_const]
    norm_num
  · set c : ℂ := 1 + Complex.I * (Δ:ℂ) with hc_def
    have hc_re : c.re = 1 := by rw [hc_def]; simp [Complex.add_re]
    have hc_im : c.im = Δ := by rw [hc_def]; simp [Complex.add_im]
    have hc_ne : c ≠ 0 := by
      intro h
      have h2 : c.im = (0:ℂ).im := by rw [h]
      rw [hc_im] at h2
      simp at h2
      exact hΔ h2
    have hderiv : ∀ v ∈ Set.uIcc (1:ℝ) 2,
        HasDerivAt (fun v : ℝ => (v:ℂ)^c / c) ((v:ℂ)^(Complex.I * (Δ:ℂ))) v := by
      intro v hv
      have hv1 : (0:ℝ) < v := by
        rcases Set.mem_uIcc.mp hv with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
      have hbase : (v:ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hv1
      have h1 : HasDerivAt (fun v : ℝ => (v:ℂ)) 1 v := by
        simpa using HasDerivAt.ofReal_comp (hasDerivAt_id v)
      have hg : HasDerivAt (fun z : ℂ => z^c) (c * (v:ℂ)^(c-1)) (v:ℂ) :=
        (Complex.hasStrictDerivAt_cpow_const hbase).hasDerivAt
      have h2 : HasDerivAt (fun v : ℝ => (v:ℂ)^c) ((c * (v:ℂ)^(c-1)) * 1) v := hg.comp v h1
      have h3 := h2.div_const c
      have hgoal : (c * (v:ℂ)^(c-1)) * 1 / c = (v:ℂ)^(Complex.I * (Δ:ℂ)) := by
        rw [mul_one, mul_div_cancel_left₀ _ hc_ne]
        have hc1 : c - 1 = Complex.I * (Δ:ℂ) := by rw [hc_def]; ring
        rw [hc1]
      rwa [hgoal] at h3
    have hint : IntervalIntegrable (fun v : ℝ => (v:ℂ)^(Complex.I*(Δ:ℂ)))
        MeasureTheory.volume 1 2 := by
      apply ContinuousOn.intervalIntegrable
      exact ContinuousOn.cpow_const (f := fun v : ℝ => (v:ℂ)) Complex.continuous_ofReal.continuousOn
        (fun v hv => Complex.ofReal_mem_slitPlane.mpr
          (by rcases Set.mem_uIcc.mp hv with ⟨h1,_⟩ | ⟨h1,_⟩ <;> linarith))
    have hmain : ∫ v in (1:ℝ)..2, (v:ℂ)^(Complex.I*(Δ:ℂ)) = ((((2:ℝ):ℂ)^c - 1)/c) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      have h1 : ((1:ℝ):ℂ)^c = 1 := by rw [Complex.ofReal_one, Complex.one_cpow]
      rw [h1, ← sub_div]
    have h2c : ‖(((2:ℝ):ℂ)^c)‖ = 2 := by
      have hsym : Complex.log (((2:ℝ):ℂ)) = ((Real.log 2 : ℝ) : ℂ) :=
        (Complex.ofReal_log (x := 2) (by norm_num)).symm
      rw [Complex.cpow_def_of_ne_zero (by norm_num : (((2:ℝ):ℂ)) ≠ 0), hsym,
        Complex.norm_exp, Complex.mul_re]
      have hr : ((Real.log 2 : ℝ) : ℂ).re = Real.log 2 := Complex.ofReal_re _
      have hi : ((Real.log 2 : ℝ) : ℂ).im = 0 := Complex.ofReal_im _
      rw [hr, hi, hc_re]
      simp only [mul_one, zero_mul, sub_zero]
      exact Real.exp_log (by norm_num)
    rw [hmain]
    have hnormc1 : (1:ℝ) ≤ ‖c‖ := by
      have h' := Complex.abs_re_le_norm c
      rwa [hc_re, abs_one] at h'
    have hnormcD : |Δ| ≤ ‖c‖ := by
      have h' := Complex.abs_im_le_norm c
      rwa [hc_im] at h'
    have hpos : (0:ℝ) < ‖c‖ := by linarith
    have hnum : ‖(((2:ℝ):ℂ)^c) - 1‖ ≤ 3 := by
      calc ‖(((2:ℝ):ℂ)^c) - 1‖ ≤ ‖(((2:ℝ):ℂ)^c)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = ‖(((2:ℝ):ℂ)^c)‖ + 1 := by simp
        _ = 3 := by rw [h2c]; norm_num
    calc ‖((((2:ℝ):ℂ)^c - 1)/c)‖ = ‖(((2:ℝ):ℂ)^c) - 1‖/‖c‖ := norm_div _ _
      _ ≤ 3/‖c‖ := div_le_div_of_nonneg_right hnum (le_of_lt hpos)
      _ ≤ 6/(1+|Δ|) := by
            have hle : 1 + |Δ| ≤ 2 * ‖c‖ := by linarith
            have hb : (0:ℝ) < 1 + |Δ| := by positivity
            rw [show (3:ℝ)/‖c‖ = 6/(2*‖c‖) by ring]
            exact div_le_div_of_nonneg_left (by norm_num) hb hle

/-- **GM (7.2) expansion.** `∫_1^2 ‖Rfun W v‖^2 dv = Re Σ_{t,t' ∈ W} ∫_1^2 v^{i(t-t')} dv`. -/
theorem R_l2_expansion (W : Finset ℝ) :
    ∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2
      = Complex.re (∑ t ∈ W, ∑ t' ∈ W,
          ∫ v in (1 : ℝ)..2, ((v : ℂ) ^ (Complex.I * ((t - t') : ℂ)))) := by
  have hpt : ∀ v ∈ Set.uIcc (1:ℝ) 2,
      ((‖Submission.GM.Rfun W v‖ ^ 2 : ℝ) : ℂ)
        = ∑ t ∈ W, ∑ t' ∈ W, (v : ℂ) ^ (Complex.I * ((t - (t':ℝ)) : ℂ)) := by
    intro v hv
    have hv1 : (0:ℝ) < v := by
      rcases Set.mem_uIcc.mp hv with ⟨h1,_⟩ | ⟨h1,_⟩ <;> linarith
    have hvne : ((v:ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt hv1
    have habs : (|v| : ℝ) = v := abs_of_pos hv1
    have hnorm : ∀ s : ℝ, ‖((v:ℂ)) ^ (Complex.I * (s:ℂ))‖ = 1 := by
      intro s; rw [Complex.norm_cpow_eq_rpow_re_of_pos hv1]; simp
    have hconj : star (Submission.GM.Rfun W v)
        = ∑ t' ∈ W, (v:ℂ) ^ (-(Complex.I * ((t':ℝ):ℂ))) := by
      rw [Submission.GM.Rfun, star_sum]
      refine Finset.sum_congr rfl fun t' ht' => ?_
      rw [habs, Complex.star_def, ← Complex.inv_eq_conj (hnorm t'), ← Complex.cpow_neg]
    calc ((‖Submission.GM.Rfun W v‖ ^ 2 : ℝ) : ℂ)
        = Submission.GM.Rfun W v * star (Submission.GM.Rfun W v) := by
          rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      _ = (∑ t ∈ W, ((v:ℂ)) ^ (Complex.I * (t:ℂ))) *
            (∑ t' ∈ W, (v:ℂ) ^ (-(Complex.I * ((t':ℝ):ℂ)))) := by
          rw [hconj]
          congr 1
          rw [Submission.GM.Rfun]
          refine Finset.sum_congr rfl fun t ht => ?_
          rw [habs]
      _ = ∑ t ∈ W, ∑ t' ∈ W, ((v:ℂ)) ^ (Complex.I * (t:ℂ)) *
            ((v:ℂ)) ^ (-(Complex.I * ((t':ℝ):ℂ))) :=
          Finset.sum_mul_sum W W _ _
      _ = ∑ t ∈ W, ∑ t' ∈ W, ((v:ℂ)) ^ (Complex.I * ((t - t') : ℂ)) := by
          refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun t' ht' => ?_
          rw [← Complex.cpow_add _ _ hvne]
          congr 1
          ring
  have hcontOn : ∀ (Δ : ℂ), ContinuousOn
      (fun v : ℝ => ((v:ℂ) ^ (Complex.I * Δ))) (Set.uIcc 1 2) := by
    intro Δ
    exact ContinuousOn.cpow_const (f := fun v : ℝ => (v:ℂ)) Complex.continuous_ofReal.continuousOn
      (fun v hv => Complex.ofReal_mem_slitPlane.mpr
        (by rcases Set.mem_uIcc.mp hv with ⟨h1,_⟩ | ⟨h1,_⟩ <;> linarith))
  have hcont : ∀ (Δ : ℂ), IntervalIntegrable
      (fun v : ℝ => ((v:ℂ) ^ (Complex.I * Δ))) MeasureTheory.volume 1 2 :=
    fun Δ => (hcontOn Δ).intervalIntegrable
  have h1 : ∫ v in (1:ℝ)..2, ((‖Submission.GM.Rfun W v‖ ^ 2 : ℝ) : ℂ)
      = ∫ v in (1:ℝ)..2, ∑ t ∈ W, ∑ t' ∈ W, (v:ℂ) ^ (Complex.I * ((t - t') : ℂ)) :=
    intervalIntegral.integral_congr hpt
  rw [intervalIntegral.integral_ofReal] at h1
  have h2 : ∫ v in (1:ℝ)..2, ∑ t ∈ W, ∑ t' ∈ W, (v:ℂ) ^ (Complex.I * ((t - t') : ℂ))
      = ∑ t ∈ W, ∑ t' ∈ W, ∫ v in (1:ℝ)..2, (v:ℂ) ^ (Complex.I * ((t - t') : ℂ)) := by
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun t ht => ?_
      rw [intervalIntegral.integral_finsetSum]
      intro t' ht'
      exact hcont ((t - t') : ℂ)
    · intro t ht
      exact (continuousOn_finsetSum W (fun t' ht' => hcontOn ((t - t') : ℂ))).intervalIntegrable
  have h3 := congrArg Complex.re h1
  simp only [Complex.ofReal_re] at h3
  rw [h2] at h3
  exact h3

/-- The elementary estimate `18 + 12 log(N^{6/5}+2) ≤ (18 + 24·3^{ε/2}/ε) N^ε` for `N ≥ 1`. -/
private lemma log_bound (ε : ℝ) (hε : 0 < ε) (N : ℕ) (hN : 1 ≤ N) :
    18 + 12 * Real.log ((N:ℝ) ^ (6/5:ℝ) + 2)
      ≤ (18 + 24 * 3 ^ (ε/2) / ε) * (N:ℝ) ^ ε := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le zero_lt_one hN1
  set x : ℝ := (N:ℝ) with hx
  have hx1 : 1 ≤ x := hN1
  have hxpos : 0 < x := hNpos
  have hP1 : (1:ℝ) ≤ x ^ ε := Real.one_le_rpow hx1 (le_of_lt hε)
  have hxT1 : (1:ℝ) ≤ x ^ (6/5:ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hlog : Real.log (x ^ (6/5:ℝ) + 2)
      ≤ 2 * (x ^ (6/5:ℝ) + 2) ^ (ε/2) / ε := by
    have h := Real.log_le_rpow_div (x := x ^ (6/5:ℝ) + 2) (ε := ε/2)
      (by positivity) (by linarith)
    have h2 : (x ^ (6/5:ℝ) + 2) ^ (ε/2) / (ε/2)
        = 2 * (x ^ (6/5:ℝ) + 2) ^ (ε/2) / ε := by
      field_simp
    linarith [h, h2.symm.le, h2.le]
  have hstep : (x ^ (6/5:ℝ) + 2) ^ (ε/2) ≤ 3 ^ (ε/2) * x ^ ε := by
    have hle : x ^ (6/5:ℝ) + 2 ≤ 3 * x ^ (6/5:ℝ) := by linarith
    have h1 : (x ^ (6/5:ℝ) + 2) ^ (ε/2) ≤ (3 * x ^ (6/5:ℝ)) ^ (ε/2) :=
      Real.rpow_le_rpow (by positivity) hle (by positivity)
    have h2 : (3 * x ^ (6/5:ℝ)) ^ (ε/2) = 3 ^ (ε/2) * x ^ (3*ε/5) := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      congr 1
      rw [← Real.rpow_mul (le_of_lt hxpos)]
      congr 1
      ring
    have h3 : x ^ (3*ε/5) ≤ x ^ ε := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h4 : (0:ℝ) ≤ 3 ^ (ε/2) := by positivity
    calc (x ^ (6/5:ℝ) + 2) ^ (ε/2) ≤ (3 * x ^ (6/5:ℝ)) ^ (ε/2) := h1
      _ = 3 ^ (ε/2) * x ^ (3*ε/5) := h2
      _ ≤ 3 ^ (ε/2) * x ^ ε := by exact mul_le_mul_of_nonneg_left h3 h4
  have hL : 12 * Real.log (x ^ (6/5:ℝ) + 2) ≤ 24 * 3 ^ (ε/2) * x ^ ε / ε := by
    have h3 : 2 * (x ^ (6/5:ℝ) + 2) ^ (ε/2) / ε ≤ 2 * (3 ^ (ε/2) * x ^ ε) / ε := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hε)
      linarith
    have h4 : 12 * (2 * (3 ^ (ε/2) * x ^ ε) / ε) = 24 * 3 ^ (ε/2) * x ^ ε / ε := by ring
    linarith [hlog, hstep, h3, h4.le, h4.ge]
  have hgoal : 18 + 12 * Real.log (x ^ (6/5:ℝ) + 2)
      ≤ (18 + 24 * 3 ^ (ε/2) / ε) * x ^ ε := by
    have h5 : 24 * 3 ^ (ε/2) * x ^ ε / ε = (24 * 3 ^ (ε/2) / ε) * x ^ ε := by ring
    have h6 : (18 + 24 * 3 ^ (ε/2) / ε) * x ^ ε
        = 18 * x ^ ε + (24 * 3 ^ (ε/2) / ε) * x ^ ε := by ring
    rw [h5] at hL
    rw [h6]
    nlinarith [hL, hP1]
  rwa [hx] at hgoal

/-- **GM Lemma 8.2** (L² bound for `R`), with `Rfun W v = Σ_{t ∈ W} |v|^{i t}` and `T = M N = N^{6/5}`.
For every `ε > 0` there is `C > 0` and `N₀` such that for `N ≥ N₀`, for every `W ⊆ [0, M N]` that is
`(M N)^ε`-separated, `∫_1^2 ‖Rfun W v‖^2 dv ≤ C * N^ε * |W|`.

Proof sketch: expand the square, `∫_1^2 v^{i(t-t')} dv ≪ 1/(1+|t-t'|)`; the diagonal gives `|W|`, and
separation gives `Σ_{t≠t'} 1/|t-t'| ≪ |W| * log(T)/T^ε ≪ |W| N^ε`. -/
theorem R_l2 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
      ∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2 ≤ C * (N : ℝ) ^ ε * (W.card : ℝ) := by
  intro ε hε
  refine ⟨18 + 24 * 3 ^ (ε/2) / ε, by positivity, 1, ?_⟩
  intro N hN W hsub hsep
  have hx1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hT1 : (1:ℝ) ≤ Submission.LargeValues.M N := Submission.LargeValues.M_ge_one hN
  have hTpos : (0:ℝ) < Submission.LargeValues.M N := Submission.LargeValues.M_pos hN
  have hδ1 : (1:ℝ) ≤ (Submission.LargeValues.M N) ^ ε := Real.one_le_rpow hT1 (le_of_lt hε)
  have hδpos : (0:ℝ) < (Submission.LargeValues.M N) ^ ε := Real.rpow_pos_of_pos hTpos ε
  have hcard0 : (0:ℝ) ≤ (W.card : ℝ) := by positivity
  have hstep1 : ∫ v in (1:ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2
      ≤ 6 * (∑ t ∈ W, ∑ t' ∈ W, 1 / (1 + |t - t'|)) := by
    rw [R_l2_expansion W]
    calc Complex.re (∑ t ∈ W, ∑ t' ∈ W,
            ∫ v in (1:ℝ)..2, (v:ℂ)^(Complex.I*((t - t') : ℂ)))
        = ∑ t ∈ W, ∑ t' ∈ W,
            Complex.re (∫ v in (1:ℝ)..2, (v:ℂ)^(Complex.I*((t - t') : ℂ))) := by
          rw [Complex.re_sum]
          refine Finset.sum_congr rfl fun t ht => ?_
          rw [Complex.re_sum]
      _ ≤ ∑ t ∈ W, ∑ t' ∈ W,
            ‖∫ v in (1:ℝ)..2, (v:ℂ)^(Complex.I*((t - t') : ℂ))‖ :=
          Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun t' ht' => Complex.re_le_norm _
      _ ≤ ∑ t ∈ W, ∑ t' ∈ W, 6 / (1 + |t - t'|) :=
          Finset.sum_le_sum fun t ht =>
            Finset.sum_le_sum fun t' ht' =>
              (by simpa [Complex.ofReal_sub] using pair_integral_bound (t - t'))
      _ = 6 * ∑ t ∈ W, ∑ t' ∈ W, 1 / (1 + |t - t'|) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t ht => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t' ht' => ?_
          ring
  have hstep2 : (∑ t ∈ W, ∑ t' ∈ W, 1 / (1 + |t - t'|))
      ≤ (W.card : ℝ) * (1 + 2 * (1 + Real.log (Submission.LargeValues.M N /
          (Submission.LargeValues.M N) ^ ε + 2)) / (Submission.LargeValues.M N) ^ ε) :=
    sep_recip_sum W ((Submission.LargeValues.M N) ^ ε) (Submission.LargeValues.M N) hδpos hsub
      (fun t ht s hs hts => hsep t ht s hs hts)
  have hstep3 : 1 + 2 * (1 + Real.log (Submission.LargeValues.M N /
          (Submission.LargeValues.M N) ^ ε + 2)) / (Submission.LargeValues.M N) ^ ε
      ≤ 1 + 2 * (1 + Real.log (Submission.LargeValues.M N + 2)) := by
    have hT0 : (0:ℝ) ≤ Submission.LargeValues.M N := le_of_lt hTpos
    have hdiv : Submission.LargeValues.M N / (Submission.LargeValues.M N) ^ ε
        ≤ Submission.LargeValues.M N := by
      rw [div_le_iff₀ hδpos]
      nlinarith [hT0, hδ1]
    have hlog : Real.log (Submission.LargeValues.M N / (Submission.LargeValues.M N) ^ ε + 2)
        ≤ Real.log (Submission.LargeValues.M N + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hb : (0:ℝ) ≤ 1 + Real.log (Submission.LargeValues.M N + 2) := by
      have h2 : (0:ℝ) ≤ Real.log (Submission.LargeValues.M N + 2) :=
        Real.log_nonneg (by linarith)
      linarith
    have h1 : 2 * (1 + Real.log (Submission.LargeValues.M N /
        (Submission.LargeValues.M N) ^ ε + 2)) / (Submission.LargeValues.M N) ^ ε
        ≤ 2 * (1 + Real.log (Submission.LargeValues.M N + 2)) := by
      rw [div_le_iff₀ hδpos]
      nlinarith [hlog, hb, hδ1]
    linarith
  have hstep4 : 1 + 2 * (1 + Real.log (Submission.LargeValues.M N + 2))
      = 3 + 2 * Real.log (Submission.LargeValues.M N + 2) := by ring
  have hnum : 3 + 2 * Real.log (Submission.LargeValues.M N + 2)
      ≤ (18 + 24 * 3 ^ (ε/2) / ε) * (N:ℝ)^ε / 6 := by
    have h := log_bound ε hε N hN
    have hM : Submission.LargeValues.M N = (N:ℝ)^(6/5:ℝ) := rfl
    rw [hM]
    linarith
  calc ∫ v in (1:ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2
      ≤ 6 * (∑ t ∈ W, ∑ t' ∈ W, 1 / (1 + |t - t'|)) := hstep1
    _ ≤ 6 * ((W.card : ℝ) * (1 + 2 * (1 + Real.log (Submission.LargeValues.M N /
          (Submission.LargeValues.M N) ^ ε + 2)) / (Submission.LargeValues.M N) ^ ε)) := by
          exact mul_le_mul_of_nonneg_left hstep2 (by norm_num)
    _ ≤ 6 * ((W.card : ℝ) * (1 + 2 * (1 + Real.log (Submission.LargeValues.M N + 2)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hcard0) (by norm_num)
          linarith [hstep3]
    _ = (W.card : ℝ) * (18 + 12 * Real.log (Submission.LargeValues.M N + 2)) := by ring
    _ ≤ (W.card : ℝ) * ((18 + 24 * 3 ^ (ε/2) / ε) * (N:ℝ)^ε) := by
          refine mul_le_mul_of_nonneg_left ?_ hcard0
          linarith [hnum]
    _ = (18 + 24 * 3 ^ (ε/2) / ε) * (N:ℝ)^ε * (W.card : ℝ) := by ring

end Work.GM.S3
