import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology

namespace Work.Diff.Dim2

/-! ## Elementary one-dimensional ODE lemmas

The main tool is the mean value theorem for a function whose derivative vanishes on an interval. -/

/-- A function whose derivative vanishes on an interval is constant there. -/
private lemma const_of_hasDerivAt_zero {ψ : ℝ → ℝ} {a b : ℝ}
    (h : ∀ u ∈ Set.Icc a b, HasDerivAt ψ 0 u) {x y : ℝ} (hx : x ∈ Set.Icc a b)
    (hy : y ∈ Set.Icc a b) : ψ x = ψ y := by
  have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
  have hmain := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := ψ) (f' := fun _ : ℝ => (0 : ℝ)) (C := 0)
    (fun u hu => (h u hu).hasDerivWithinAt) (fun _ _ => by simp) hx hy
  have h0 : ‖ψ y - ψ x‖ = 0 := by
    have h' : ‖ψ y - ψ x‖ ≤ 0 := by simpa using hmain
    exact le_antisymm h' (norm_nonneg _)
  exact (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm

/-- On an interval where `G` takes its values in the window `[lo,hi]`, the function goes down at
unit speed. -/
private lemma sub_eq_of_mem_of_hasDerivAt {G : ℝ → ℝ} {lo hi a b : ℝ}
    (hmem : ∀ u ∈ Set.Icc a b, G u ∈ Set.Icc lo hi)
    (hderiv : ∀ u : ℝ, G u ∈ Set.Icc lo hi → HasDerivAt G (-1) u)
    {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) : G y - G x = -(y - x) := by
  have hψ : ∀ u ∈ Set.Icc a b, HasDerivAt (fun v : ℝ => G v + v) 0 u := by
    intro u hu
    have h1 : HasDerivAt (fun v : ℝ => G v + v) (-1 + 1) u :=
      (hderiv u (hmem u hu)).add (hasDerivAt_id u)
    have h2 : (-1 : ℝ) + 1 = 0 := by norm_num
    rw [h2] at h1
    exact h1
  have h3 := const_of_hasDerivAt_zero hψ hx hy
  change G x + x = G y + y at h3
  linarith

/-- The error form of `HasDerivAt G (-1) x`. -/
private lemma hasDerivAt_neg_one_bound {G : ℝ → ℝ} {x : ℝ} (h : HasDerivAt G (-1) x) :
    ∃ δ > 0, ∀ u : ℝ, |u - x| < δ → |G u - G x + (u - x)| ≤ (1 / 2) * |u - x| := by
  have hb := h.isLittleO.bound (by norm_num : (0 : ℝ) < 1 / 2)
  rw [Metric.eventually_nhds_iff] at hb
  obtain ⟨δ, hδ, hb⟩ := hb
  refine ⟨δ, hδ, fun u hu => ?_⟩
  have h1 := hb (show dist u x < δ by rwa [Real.dist_eq])
  have h2 : G u - G x - (u - x) • (-1 : ℝ) = G u - G x + (u - x) := by
    simp only [smul_eq_mul]
    ring
  rwa [h2, Real.norm_eq_abs, Real.norm_eq_abs] at h1

/-- **Downward flow.**  Starting from a point in the window, `G` slides down at unit speed until it
reaches `lo` and then stays below `lo`. -/
private lemma flow_down_forward
    {lo hi : ℝ} (hlohi : lo < hi) {G : ℝ → ℝ} (hG : Continuous G)
    (hderiv : ∀ s : ℝ, G s ∈ Set.Icc lo hi → HasDerivAt G (-1) s)
    {s₀ : ℝ} (hs₀ : G s₀ ∈ Set.Icc lo hi) :
    (∀ s ∈ Set.Icc s₀ (s₀ + (G s₀ - lo)), G s = G s₀ - (s - s₀)) ∧
    (∀ s, s₀ + (G s₀ - lo) < s → G s < lo) := by
  set g0 : ℝ := G s₀ with hg0
  set T : ℝ := s₀ + (g0 - lo) with hT
  have hg0lo : lo ≤ g0 := hs₀.1
  have hg0hi : g0 ≤ hi := hs₀.2
  have hs₀T : s₀ ≤ T := by rw [hT]; linarith
  have hs₀Tmem : s₀ ∈ Set.Icc s₀ T := ⟨le_rfl, hs₀T⟩
  have hmain : ∀ s ∈ Set.Icc s₀ T, G s = g0 - (s - s₀) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s₁, hs₁, hs₁ne⟩ := hcon
    let B : Set ℝ := {u | u ∈ Set.Icc s₀ T ∧ G u ≠ g0 - (u - s₀)}
    have hBne : B.Nonempty := ⟨s₁, hs₁, hs₁ne⟩
    have hBbdd : BddBelow B := ⟨s₀, fun y hy => hy.1.1⟩
    set t : ℝ := sInf B with ht
    have htle : t ≤ s₁ := csInf_le hBbdd ⟨hs₁, hs₁ne⟩
    have htT : t ≤ T := le_trans htle hs₁.2
    have hs₀t : s₀ ≤ t := le_csInf hBne (fun b hb => hb.1.1)
    have hbelow : ∀ u : ℝ, s₀ ≤ u → u < t → G u = g0 - (u - s₀) := by
      intro u hsu hut
      by_contra hne
      have huB : u ∈ B := ⟨⟨hsu, le_trans (le_of_lt hut) htT⟩, hne⟩
      have := csInf_le hBbdd huB
      linarith
    -- window membership of the formula
    have hwindow : ∀ u : ℝ, s₀ ≤ u → u ≤ T → G u = g0 - (u - s₀) → G u ∈ Set.Icc lo hi := by
      intro u hsu huT h
      have h1 : u - s₀ ≤ g0 - lo := by rw [hT] at huT; linarith
      have h2 : 0 ≤ u - s₀ := by linarith
      rw [h]
      exact ⟨by linarith, by linarith⟩
    have hkey : (∀ u ∈ Set.Icc s₀ T, G u ∈ Set.Icc lo hi) ∨
        (∃ b : ℝ, t < b ∧ b ≤ T ∧ ∀ u ∈ Set.Icc s₀ b, G u ∈ Set.Icc lo hi) := by
      rcases lt_or_eq_of_le hs₀t with ht_gt | ht_eq
      · -- `s₀ < t`
        have hGt : G t = g0 - (t - s₀) := by
          have hlin : Filter.Tendsto (fun u : ℝ => g0 - (u - s₀)) (𝓝[<] t)
              (𝓝 (g0 - (t - s₀))) :=
            ((continuous_const.sub (continuous_id.sub continuous_const)).tendsto t).mono_left
              nhdsWithin_le_nhds
          have h1 : Filter.Tendsto G (𝓝[<] t) (𝓝 (g0 - (t - s₀))) := by
            refine Filter.Tendsto.congr' ?_ hlin
            filter_upwards [self_mem_nhdsWithin,
              nhdsWithin_le_nhds (Ioi_mem_nhds ht_gt)] with u hu hsu
            exact (hbelow u (le_of_lt hsu) hu).symm
          have h2 : Filter.Tendsto G (𝓝[<] t) (𝓝 (G t)) :=
            hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
          exact tendsto_nhds_unique h2 h1
        have hmem_left : ∀ u : ℝ, s₀ ≤ u → u ≤ t → G u ∈ Set.Icc lo hi := by
          intro u hsu hut
          rcases lt_or_eq_of_le hut with hult | hult
          · exact hwindow u hsu (le_trans (le_of_lt hult) htT) (hbelow u hsu hult)
          · rw [hult]
            exact hwindow t hs₀t htT hGt
        rcases lt_or_eq_of_le htT with ht_ltT | ht_eqT
        · rcases lt_or_ge (G t) hi with hlt_hi | hge_hi
          · by_cases hlo : lo < G t
            · -- `lo < G t < hi`
              obtain ⟨h, hh, hhprop⟩ : ∃ h > 0, ∀ u : ℝ, dist u t < h →
                  lo < G u ∧ G u < hi := by
                have hnt : {u : ℝ | lo < G u ∧ G u < hi} ∈ 𝓝 t :=
                  Filter.inter_mem (hG.continuousAt (isOpen_Ioi.mem_nhds hlo))
                    (hG.continuousAt (isOpen_Iio.mem_nhds hlt_hi))
                obtain ⟨h, hh, hhsub⟩ := Metric.mem_nhds_iff.mp hnt
                exact ⟨h, hh, fun u hu => hhsub (by rwa [Metric.mem_ball])⟩
              refine Or.inr ⟨min (t + h / 2) T, lt_min (by linarith) ht_ltT,
                min_le_right _ _, ?_⟩
              intro u hu
              rcases le_or_gt u t with hut | hut
              · exact hmem_left u hu.1 hut
              · have hd : dist u t < h := by
                  rw [Real.dist_eq, abs_lt]
                  exact ⟨by linarith [hu.1, hs₀t],
                    by linarith [le_trans hu.2 (min_le_left _ _)]⟩
                exact ⟨(hhprop u hd).1.le, (hhprop u hd).2.le⟩
            · -- `G t = lo` with `t < T` is impossible
              exfalso
              push Not at hlo
              have h1 : G t = lo := le_antisymm hlo (hmem_left t hs₀t le_rfl).1
              have : t = T := by rw [hGt] at h1; rw [hT]; linarith
              linarith
          · -- `G t = hi` with `s₀ < t` is impossible
            exfalso
            have hGhi : G t = hi := le_antisymm (hmem_left t hs₀t le_rfl).2 hge_hi
            rw [hGt] at hGhi
            linarith [hg0hi]
        · -- `t = T`
          refine Or.inl ?_
          intro u hu
          rw [← ht_eqT] at hu
          exact hmem_left u hu.1 hu.2
      · -- `t = s₀`
        rcases lt_or_ge (G s₀) hi with hlt_hi | hge_hi
        · by_cases hlo : lo < G s₀
          · -- `lo < G s₀ < hi`
            obtain ⟨h, hh, hhprop⟩ : ∃ h > 0, ∀ u : ℝ, dist u s₀ < h →
                lo < G u ∧ G u < hi := by
              have hnt : {u : ℝ | lo < G u ∧ G u < hi} ∈ 𝓝 s₀ :=
                Filter.inter_mem (hG.continuousAt (isOpen_Ioi.mem_nhds hlo))
                  (hG.continuousAt (isOpen_Iio.mem_nhds hlt_hi))
              obtain ⟨h, hh, hhsub⟩ := Metric.mem_nhds_iff.mp hnt
              exact ⟨h, hh, fun u hu => hhsub (by rwa [Metric.mem_ball])⟩
            have hs₀T' : s₀ < T := by rw [hT]; linarith
            have htT' : t < T := by rw [← ht_eq]; exact hs₀T'
            refine Or.inr ⟨min (s₀ + h / 2) T, lt_min (by linarith) htT',
              min_le_right _ _, ?_⟩
            intro u hu
            rcases le_or_gt u s₀ with hus | hus
            · rw [le_antisymm hus hu.1]; exact hs₀
            · have hd : dist u s₀ < h := by
                rw [Real.dist_eq, abs_lt]
                exact ⟨by linarith [hu.1], by linarith [le_trans hu.2 (min_le_left _ _)]⟩
              exact ⟨(hhprop u hd).1.le, (hhprop u hd).2.le⟩
          · -- `G s₀ = lo`, so `T = s₀`
            refine Or.inl ?_
            push Not at hlo
            have h1 : G s₀ = lo := le_antisymm hlo hs₀.1
            have hTs₀ : T = s₀ := by rw [hT, ← h1]; ring
            intro u hu
            have hle : u ≤ s₀ := by rw [hTs₀] at hu; exact hu.2
            have : u = s₀ := le_antisymm hle hu.1
            rw [this]; exact hs₀
        · -- `G s₀ = hi` : the derivative at `s₀`
          have hg0hi' : g0 = hi := le_antisymm hs₀.2 (by rw [hg0]; exact hge_hi)
          have hGhi : G s₀ = hi := by rw [← hg0]; exact hg0hi'
          obtain ⟨h, hh, hb⟩ := hasDerivAt_neg_one_bound (hderiv s₀ hs₀)
          have hs₀T' : s₀ < T := by rw [hT, hg0hi']; linarith
          have htT' : t < T := by rw [← ht_eq]; exact hs₀T'
          set e : ℝ := min h ((hi - lo) / 3) with he
          have hepos : 0 < e := lt_min hh (by linarith)
          refine Or.inr ⟨min (s₀ + e / 2) T, lt_min (by linarith) htT',
            min_le_right _ _, ?_⟩
          intro u hu
          rcases le_or_gt u s₀ with hus | hus
          · rw [le_antisymm hus hu.1]; exact hs₀
          · have hud : u - s₀ < h := by
              have h' : u ≤ s₀ + e / 2 := le_trans hu.2 (min_le_left _ _)
              have h'' : e ≤ h := min_le_left _ _
              linarith
            have h1 : |G u - G s₀ + (u - s₀)| ≤ (1 / 2) * (u - s₀) := by
              have h2 := hb u (by
                rw [abs_of_pos (show (0 : ℝ) < u - s₀ by linarith)]
                exact hud)
              rwa [abs_of_pos (show (0 : ℝ) < u - s₀ by linarith)] at h2
            have h3 := abs_le.mp h1
            constructor
            · have h4 : 3 * (u - s₀) ≤ (hi - lo) / 2 := by
                have h5 : u ≤ s₀ + e / 2 := le_trans hu.2 (min_le_left _ _)
                have h6 : e ≤ (hi - lo) / 3 := min_le_right _ _
                linarith
              linarith
            · linarith
    rcases hkey with hall | ⟨b, htb, hbT, hbprop⟩
    · -- contradiction with `s₁ ∈ B`
      have h := sub_eq_of_mem_of_hasDerivAt hall hderiv hs₀Tmem hs₁
      exact hs₁ne (by rw [hg0]; linarith)
    · -- contradiction with `t = sInf B`
      have hbform : ∀ w ∈ Set.Icc s₀ b, G w = g0 - (w - s₀) := by
        intro w hw
        have hsb : s₀ ≤ b := le_trans hs₀t (le_of_lt htb)
        have h := sub_eq_of_mem_of_hasDerivAt hbprop hderiv (x := s₀) (y := w)
          (⟨le_rfl, hsb⟩ : s₀ ∈ Set.Icc s₀ b) hw
        rw [hg0] at ⊢
        linarith
      obtain ⟨w, hwB, hwb⟩ := (csInf_lt_iff hBbdd hBne).mp htb
      have hwmem : w ∈ Set.Icc s₀ b :=
        ⟨le_trans hs₀t (csInf_le hBbdd hwB), le_of_lt hwb⟩
      exact hwB.2 (hbform w hwmem)
  refine ⟨hmain, ?_⟩
  have hTval : G T = lo := by
    have h := hmain T ⟨hs₀T, le_rfl⟩
    rw [h, hT]; ring
  intro s hsT
  by_contra hcon
  push Not at hcon
  -- points above `T` where `G` is back in `[lo,∞)`
  set B : Set ℝ := {u | T < u ∧ u ≤ s ∧ lo ≤ G u} with hBdef
  have hBmem : ∀ u : ℝ, u ∈ B ↔ T < u ∧ u ≤ s ∧ lo ≤ G u := by
    intro u; rw [hBdef, Set.mem_ofPred_eq]
  have hBs : s ∈ B := (hBmem s).mpr ⟨hsT, le_rfl, hcon⟩
  have hBne : B.Nonempty := ⟨s, hBs⟩
  have hBbdd : BddBelow B := ⟨T, fun y hy => le_of_lt ((hBmem y).mp hy).1⟩
  set u₁ : ℝ := sInf B with hu₁
  have hu₁s : u₁ ≤ s := csInf_le hBbdd hBs
  have hu₁T : T < u₁ := by
    obtain ⟨h, hh, hb⟩ := hasDerivAt_neg_one_bound
      (hderiv T (by rw [hTval]; exact ⟨le_rfl, le_of_lt hlohi⟩))
    have hno : ∀ u : ℝ, T < u → u < T + h → G u < lo := by
      intro u hTu hu
      have h1 : |G u - G T + (u - T)| ≤ (1 / 2) * (u - T) := by
        have h2 := hb u (by
          rw [abs_of_pos (show (0 : ℝ) < u - T by linarith)]
          linarith)
        rwa [abs_of_pos (show (0 : ℝ) < u - T by linarith)] at h2
      have h3 := (abs_le.mp h1).2
      rw [hTval] at h3
      linarith
    have hsgt : T + h ≤ s := by
      by_contra hlt
      push Not at hlt
      obtain ⟨u, huB⟩ := hBne
      obtain ⟨huT, hus, hulo⟩ := (hBmem u).mp huB
      exact absurd (hno u huT (lt_of_le_of_lt hus hlt)) (not_lt.mpr hulo)
    refine lt_of_lt_of_le (by linarith : T < T + h) (le_csInf hBne ?_)
    intro y hy
    by_contra hlt
    push Not at hlt
    obtain ⟨hyT, hys, hylo⟩ := (hBmem y).mp hy
    exact absurd (hno y hyT hlt) (not_lt.mpr hylo)
  have hbelow_u₁ : ∀ u : ℝ, T < u → u < u₁ → G u < lo := by
    intro u hTu hu
    have : u ∉ B := fun hmem => by
      have := csInf_le hBbdd hmem
      linarith
    exact not_le.mp (fun hlo => this ((hBmem u).mpr ⟨hTu, le_trans (le_of_lt hu) hu₁s, hlo⟩))
  have hu₁le : G u₁ ≤ lo := by
    have hlim : Filter.Tendsto G (𝓝[<] u₁) (𝓝 (G u₁)) :=
      hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hu₁T)] with u hu hTu
    exact le_of_lt (hbelow_u₁ u hTu hu)
  have hu₁mem : lo ≤ G u₁ := by
    have h1 : u₁ ∈ closure B := csInf_mem_closure hBne hBbdd
    have h2 : closure B ⊆ {u : ℝ | lo ≤ G u} :=
      closure_minimal (fun y hy => ((hBmem y).mp hy).2.2) (isClosed_le continuous_const hG)
    exact h2 h1
  have hu₁G : G u₁ = lo := le_antisymm hu₁le hu₁mem
  obtain ⟨h, hh, hb⟩ := hasDerivAt_neg_one_bound
    (hderiv u₁ (by rw [hu₁G]; exact ⟨le_rfl, le_of_lt hlohi⟩))
  set v : ℝ := (max T (u₁ - h) + u₁) / 2 with hv
  have hvT : T < v := by
    have h1 : T ≤ max T (u₁ - h) := le_max_left _ _
    rw [hv]; linarith
  have hvu₁ : v < u₁ := by
    have h1 : u₁ - h < u₁ := by linarith
    have h2 : max T (u₁ - h) < u₁ := max_lt hu₁T h1
    rw [hv]; linarith
  have hvlo : G v < lo := hbelow_u₁ v hvT hvu₁
  have hvgt : lo < G v := by
    have hvu : u₁ - v < h := by
      have h1 : u₁ - h < v := by
        have h2 : u₁ - h ≤ max T (u₁ - h) := le_max_right _ _
        rw [hv]; linarith
      linarith
    have h1 : |G v - G u₁ + (v - u₁)| ≤ (1 / 2) * (u₁ - v) := by
      have h2 := hb v (by
        rw [abs_of_neg (show v - u₁ < 0 by linarith)]
        linarith)
      have h3 : |v - u₁| = u₁ - v := by
        rw [abs_of_neg (show v - u₁ < 0 by linarith)]
        ring
      rwa [h3] at h2
    have h2 := (abs_le.mp h1).1
    rw [hu₁G] at h2
    linarith
  linarith

/-- **Upward flow**, obtained from the downward one by negating the values. -/
private lemma flow_up_forward
    {lo hi : ℝ} (hlohi : lo < hi) {F : ℝ → ℝ} (hF : Continuous F)
    (hderiv : ∀ s : ℝ, F s ∈ Set.Icc lo hi → HasDerivAt F 1 s)
    {t₀ : ℝ} (ht₀ : F t₀ ∈ Set.Icc lo hi) :
    (∀ s ∈ Set.Icc t₀ (t₀ + (hi - F t₀)), F s = F t₀ + (s - t₀)) ∧
    (∀ s, t₀ + (hi - F t₀) < s → hi < F s) := by
  have hder : ∀ s : ℝ, -F s ∈ Set.Icc (-hi) (-lo) →
      HasDerivAt (fun u : ℝ => -F u) (-1) s := by
    intro s hs
    have hs' : F s ∈ Set.Icc lo hi := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    convert (hderiv s hs').neg using 1
  have hstart : -F t₀ ∈ Set.Icc (-hi) (-lo) := ⟨by linarith [ht₀.2], by linarith [ht₀.1]⟩
  obtain ⟨h1, h2⟩ := flow_down_forward (lo := -hi) (hi := -lo) (by linarith)
    (G := fun u : ℝ => -F u) hF.neg hder hstart
  have hkey : -F t₀ - -hi = hi - F t₀ := by ring
  constructor
  · intro s hs
    have hs' : s ∈ Set.Icc t₀ (t₀ + (-F t₀ - -hi)) := by
      rw [Set.mem_Icc] at hs ⊢
      exact ⟨hs.1, by rw [hkey]; exact hs.2⟩
    have h := h1 s hs'
    linarith
  · intro s hs
    have h := h2 s (by rw [hkey]; exact hs)
    linarith

/-- **Downward flow, backwards in time**, obtained from the upward flow by reversing time. -/
private lemma flow_down_backward
    {lo hi : ℝ} (hlohi : lo < hi) {G : ℝ → ℝ} (hG : Continuous G)
    (hderiv : ∀ s : ℝ, G s ∈ Set.Icc lo hi → HasDerivAt G (-1) s)
    {s₀ : ℝ} (hs₀ : G s₀ ∈ Set.Icc lo hi) :
    (∀ s ∈ Set.Icc (s₀ - (hi - G s₀)) s₀, G s = G s₀ + (s₀ - s)) ∧
    (∀ s, s < s₀ - (hi - G s₀) → hi < G s) := by
  have hcont : Continuous (fun u : ℝ => G (s₀ - u)) :=
    hG.comp (continuous_const.sub continuous_id)
  have hder : ∀ u : ℝ, G (s₀ - u) ∈ Set.Icc lo hi →
      HasDerivAt (fun v : ℝ => G (s₀ - v)) 1 u := by
    intro u hu
    have h1 : HasDerivAt (fun v : ℝ => s₀ - v) (-1) u := by
      convert (hasDerivAt_const (x := u) (c := s₀)).sub (hasDerivAt_id u) using 1
      · ext x; rfl
      · ring
    convert (hderiv (s₀ - u) hu).comp u h1 using 1
    · ext x; rfl
    · ring
  obtain ⟨h1, h2⟩ := flow_up_forward (F := fun u : ℝ => G (s₀ - u)) (t₀ := 0) hlohi hcont hder
    (by simpa using hs₀)
  have h1' : ∀ s ∈ Set.Icc 0 (hi - G s₀), G (s₀ - s) = G s₀ + s := by
    intro s hs
    have hs' : s ∈ Set.Icc 0 (0 + (hi - (fun u : ℝ => G (s₀ - u)) 0)) := by
      rw [Set.mem_Icc] at hs ⊢
      exact ⟨hs.1, by simpa using hs.2⟩
    simpa using h1 s hs'
  have h2' : ∀ s, hi - G s₀ < s → hi < G (s₀ - s) := by
    intro s hs
    have hs' : 0 + (hi - (fun u : ℝ => G (s₀ - u)) 0) < s := by simpa using hs
    simpa using h2 s hs'
  constructor
  · intro s hs
    have hs' : s₀ - s ∈ Set.Icc 0 (hi - G s₀) := by
      rw [Set.mem_Icc] at hs ⊢
      exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h := h1' (s₀ - s) hs'
    simpa only [show s₀ - (s₀ - s) = s by ring] using h
  · intro s hs
    have h := h2' (s₀ - s) (by linarith)
    simpa only [show s₀ - (s₀ - s) = s by ring] using h

/-- 1-D interval analysis for an ODE with constant slope `-1`.  Let `G : ℝ → ℝ` be continuous
with `HasDerivAt G (-1) s` at every `s` whose value lies in the window `[lo, hi]`.  Then, starting
from a point `s₀` with `G s₀ ∈ [lo, hi]`, the function `G` slides down through the window at unit
speed until it reaches `lo` (clauses 1, 2), and slides up at unit speed going backwards until it
leaves the window at `hi` (clauses 3, 4).  Clause 5 is the consequent **uniqueness** of the level
`G = G s₀`. -/
theorem flow_g_interval
    {lo hi : ℝ} (hlohi : lo < hi)
    {G : ℝ → ℝ} (hG : Continuous G)
    (hderiv : ∀ s : ℝ, G s ∈ Set.Icc lo hi → HasDerivAt G (-1) s)
    {s₀ : ℝ} (hs₀ : G s₀ ∈ Set.Icc lo hi) :
    (∀ s ∈ Set.Icc s₀ (s₀ + (G s₀ - lo)), G s = G s₀ - (s - s₀)) ∧
    (∀ s, s₀ + (G s₀ - lo) < s → G s < lo) ∧
    (∀ s ∈ Set.Icc (s₀ - (hi - G s₀)) s₀, G s = G s₀ + (s₀ - s)) ∧
    (∀ s, s < s₀ - (hi - G s₀) → hi < G s) ∧
    (∀ s₁ s₂ : ℝ, G s₁ = G s₀ → G s₂ = G s₀ → s₁ = s₂) := by
  obtain ⟨hfwd, hfwd'⟩ := flow_down_forward hlohi hG hderiv hs₀
  obtain ⟨hbwd, hbwd'⟩ := flow_down_backward hlohi hG hderiv hs₀
  have hlevel : ∀ s : ℝ, G s = G s₀ → s = s₀ := by
    intro s hs
    rcases le_or_gt s₀ s with h | h
    · rcases le_or_gt s (s₀ + (G s₀ - lo)) with h2 | h2
      · have := hfwd s ⟨h, h2⟩
        linarith
      · have := hfwd' s h2
        linarith [hs₀.1]
    · rcases le_or_gt (s₀ - (hi - G s₀)) s with h2 | h2
      · have := hbwd s ⟨h2, le_of_lt h⟩
        linarith
      · have := hbwd' s h2
        linarith [hs₀.2]
  exact ⟨hfwd, hfwd', hbwd, hbwd',
    fun s₁ s₂ h₁ h₂ => by rw [hlevel s₁ h₁, hlevel s₂ h₂]⟩

end Work.Diff.Dim2
