import Mathlib

/-!
# `eq_of_deriv_eq_one`

If `u : ℝ → ℝ` is continuous, `u 0 ∈ [a,b]`, and `u` has derivative `1` at every point `t`
with `u t ∈ [a,b]`, then `u` agrees with the straight line `t ↦ u 0 + t` on the whole set
`{t | u 0 + t ∈ [a,b]}`.

The mathematical content is the uniqueness of the solution of the ODE `u' = 1` on the strip
`[a,b]`: the solution leaves the strip (in the linear variable) exactly at `t = b - (u 0)`, and
before that it is pinned to the line.
-/

open Filter
open scoped Topology

namespace Work.Drive.N2

/-- Local form of `HasDerivAt f 1 x` with `f' = 1 > 0`: strictly to the right of `x` and close
enough, `f` is strictly larger than `f x`. -/
private lemma exists_gt_of_hasDerivAt_one {u : ℝ → ℝ} {x : ℝ} (h : HasDerivAt u 1 x) :
    ∃ δ > 0, ∀ y, x < y → y < x + δ → u x < u y := by
  have h1 : ∀ᶠ y in 𝓝[≠] x, slope u x y ∈ Set.Ioi (1/2 : ℝ) :=
    h.tendsto_slope.eventually (Ioi_mem_nhds (by norm_num))
  rw [eventually_nhdsWithin_iff] at h1
  rw [Metric.eventually_nhds_iff] at h1
  obtain ⟨δ, hδ, hδ'⟩ := h1
  refine ⟨δ, hδ, fun y hxy hyδ => ?_⟩
  have hyne : y ≠ x := ne_of_gt hxy
  have hdy : dist y x < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hxy)]
    linarith
  have hvy : (1/2 : ℝ) < (y - x)⁻¹ • (u y - u x) := hδ' hdy hyne
  rw [smul_eq_mul] at hvy
  have hpos : 0 < (y - x)⁻¹ := inv_pos.mpr (sub_pos.mpr hxy)
  have hmul : 0 < (y - x)⁻¹ * (u y - u x) := lt_trans (by norm_num) hvy
  nlinarith [hmul, hpos]

/-- If `g` has derivative `0` at every point of `[s,t]` and `g s = 0`, then `g t = 0`
(mean value theorem). -/
private lemma eq_zero_of_deriv_zero {g : ℝ → ℝ} {s t : ℝ} (hst : s < t)
    (hgs : g s = 0) (hg : ∀ x ∈ Set.Icc s t, HasDerivAt g 0 x) : g t = 0 := by
  have hcont : ContinuousOn g (Set.Icc s t) :=
    fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ g (Set.Ioo s t) :=
    fun x hx => (hg x (Set.Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
  obtain ⟨ξ, hξ, hξ'⟩ := exists_deriv_eq_slope g hst hcont hdiff
  have h0 : deriv g ξ = 0 := (hg ξ (Set.Ioo_subset_Icc_self hξ)).deriv
  have hξ0 : (g t - g s) / (t - s) = 0 := by rw [← hξ', h0]
  have hts : t - s ≠ 0 := by linarith
  have hcancel := mul_div_cancel₀ (g t - g s) hts
  rw [hξ0, mul_zero] at hcancel
  linarith

/-- `u` stays on the line `c + ·` for a while to the right of a point `T` at which it is on
that line, provided `c + T < b` (so that the strip `[a,b]` is not yet exhausted). -/
private lemma local_extension {u : ℝ → ℝ} (hu : Continuous u) {a b c T : ℝ}
    (huT : u T = c + T) (ha : a ≤ c + T) (hTb : c + T < b)
    (hd : ∀ t, u t ∈ Set.Icc a b → HasDerivAt u 1 t) :
    ∃ δ > 0, ∀ y ∈ Set.Icc T (T + δ), u y = c + y := by
  have hmemT : u T ∈ Set.Icc a b := by
    rw [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := exists_gt_of_hasDerivAt_one (hd T hmemT)
  have hbT : u T < b := by rw [huT]; exact hTb
  have hb₂ : ∀ᶠ y in 𝓝 T, u y < b := hu.continuousAt.eventually (Iio_mem_nhds hbT)
  rw [Metric.eventually_nhds_iff] at hb₂
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hb₂
  refine ⟨min δ₁ δ₂ / 2, by positivity, fun y hy => ?_⟩
  have hlt₁ : min δ₁ δ₂ / 2 < δ₁ := by have := min_le_left δ₁ δ₂; linarith
  have hlt₂ : min δ₁ δ₂ / 2 < δ₂ := by have := min_le_right δ₁ δ₂; linarith
  rw [Set.mem_Icc] at hy
  rcases eq_or_lt_of_le hy.1 with h | hyT
  · rw [← h]; exact huT
  · have key : (fun z => u z - (c + z)) y = 0 := by
      apply eq_zero_of_deriv_zero hyT (by simp [huT])
      intro z hz
      rw [Set.mem_Icc] at hz
      have hzmem : u z ∈ Set.Icc a b := by
        rw [Set.mem_Icc]
        refine ⟨?_, ?_⟩
        · rcases eq_or_lt_of_le hz.1 with h | h
          · rw [← h]; linarith
          · have h1 : u T < u z := hδ₁ z h (by linarith [hz.2])
            rw [huT] at h1; linarith
        · rcases eq_or_lt_of_le hz.1 with h | h
          · rw [← h]; linarith
          · have hd2 : dist z T < δ₂ := by
              rw [Real.dist_eq, abs_of_pos (sub_pos.mpr h)]
              linarith [hz.2]
            exact le_of_lt (hδ₂ hd2)
      have h2 : HasDerivAt (fun z => c + z) 1 z := (hasDerivAt_id z).const_add c
      have h3 : HasDerivAt (fun w => u w - (c + w)) (1 - 1 : ℝ) z := (hd z hzmem).sub h2
      simpa only [Pi.sub_apply, sub_self] using h3
    simp only at key
    linarith

/-- **Global extension.** If `u T = c + T`, `a ≤ c + T` and `T < b - c`, then `u` agrees with
the line `c + ·` on all of `[T, b - c]`. -/
private lemma extension_step {u : ℝ → ℝ} (hu : Continuous u) {a b c T : ℝ}
    (huT : u T = c + T) (ha : a ≤ c + T) (hTb : T < b - c)
    (hd : ∀ t, u t ∈ Set.Icc a b → HasDerivAt u 1 t) :
    ∀ ξ ∈ Set.Icc T (b - c), u ξ = c + ξ := by
  set g : ℝ → ℝ := fun z => u z - (c + z) with hgdef
  have hgcont : Continuous g := by
    rw [hgdef]; exact hu.sub (continuous_const.add continuous_id)
  have hZclosed : IsClosed {z | g z = 0} := isClosed_singleton.preimage hgcont
  have hderg : ∀ w, u w ∈ Set.Icc a b → HasDerivAt g 0 w := by
    intro w hw
    have h2 : HasDerivAt (fun z => c + z) 1 w := (hasDerivAt_id w).const_add c
    have h3 : HasDerivAt (fun v => u v - (c + v)) (1 - 1 : ℝ) w := (hd w hw).sub h2
    rw [hgdef]
    simpa only [Pi.sub_apply, sub_self] using h3
  have hTmem : u T ∈ Set.Icc a b := by
    rw [Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
  have hgT : g T = 0 := by rw [hgdef]; simp [huT]
  by_cases hS : ∃ x ∈ Set.Ioc T (b - c), u x ∉ Set.Icc a b
  · exfalso
    set S : Set ℝ := {x | x ∈ Set.Ioc T (b - c) ∧ u x ∉ Set.Icc a b} with hSdef
    obtain ⟨x₀, hx₀⟩ := hS
    have hSne : S.Nonempty := ⟨x₀, hx₀⟩
    have hSbdd : BddBelow S := ⟨T, fun y hy => le_of_lt hy.1.1⟩
    set E := sInf S with hEdef
    have hET : T ≤ E := by rw [hEdef]; exact le_csInf hSne (fun y hy => le_of_lt hy.1.1)
    have hEb : E ≤ b - c := by
      rw [hEdef]; exact le_trans (csInf_le hSbdd hx₀) hx₀.1.2
    have hgood : ∀ x, T < x → x < E → u x ∈ Set.Icc a b := by
      intro x hTx hxE
      by_contra hx
      have hxS : x ∈ S := ⟨⟨hTx, le_of_lt (by linarith : x < b - c)⟩, hx⟩
      have hle : E ≤ x := by rw [hEdef]; exact csInf_le hSbdd hxS
      linarith
    rcases eq_or_lt_of_le hET with hETeq | hETlt
    · -- the bad set starts immediately at `T`
      have hTbT : c + T < b := by linarith
      obtain ⟨δ, hδpos, hδ⟩ := local_extension hu huT ha hTbT hd
      have hlt : sInf S < T + δ := by rw [← hEdef, hETeq]; linarith
      obtain ⟨y, hyS, hyδ⟩ := (csInf_lt_iff hSbdd hSne).mp hlt
      have hyT : T < y := hyS.1.1
      have hmem : u y = c + y := hδ y (by rw [Set.mem_Icc]; exact ⟨le_of_lt hyT, le_of_lt hyδ⟩)
      have hyI : c + y ∈ Set.Icc a b := by
        rw [Set.mem_Icc]; exact ⟨by linarith, by linarith [hyS.1.2]⟩
      rw [← hmem] at hyI
      exact hyS.2 hyI
    · -- `E > T`: on `(T,E)` `u` is on the line, so at `E` it is on the line and on the
      -- boundary of the strip, which is impossible
      have hEeq : u E = c + E := by
        have hsub : Set.Ioo T E ⊆ {z | g z = 0} := by
          intro z hz
          have hres := eq_zero_of_deriv_zero (g := g) hz.1 hgT (fun w hw => ?_)
          · exact hres
          · rw [Set.mem_Icc] at hw
            rcases eq_or_lt_of_le hw.1 with h | h
            · rw [← h]; exact hderg T hTmem
            · exact hderg w (hgood w h (by linarith [hw.2, hz.2]))
        have hEcl : E ∈ closure (Set.Ioo T E) := by
          rw [closure_Ioo (ne_of_lt hETlt)]; exact ⟨hET, le_rfl⟩
        have hcl : E ∈ closure {z | g z = 0} := closure_mono hsub hEcl
        rw [hZclosed.closure_eq] at hcl
        have hgE : g E = 0 := hcl
        have : u E - (c + E) = 0 := by simpa only [hgdef] using hgE
        linarith
      have huEI : u E ∈ Set.Icc a b := by
        rw [Set.mem_Icc]; exact ⟨by linarith, by linarith [hEb]⟩
      have hEclS : E ∈ closure S := by rw [hEdef]; exact csInf_mem_closure hSne hSbdd
      have huE2 : u E ∈ (Set.Ioo a b)ᶜ := by
        have himg : u E ∈ closure (u '' S) :=
          image_closure_subset_closure_image hu ⟨E, hEclS, rfl⟩
        have hsub2 : u '' S ⊆ (Set.Icc a b)ᶜ := by
          rintro z ⟨y, hyS, rfl⟩
          simpa using hyS.2
        have := closure_mono hsub2 himg
        rwa [closure_compl, interior_Icc] at this
      have hab2 : u E = a ∨ u E = b := by
        rw [Set.mem_Icc] at huEI
        simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and, not_lt] at huE2
        rcases lt_or_eq_of_le huEI.1 with h | h
        · exact Or.inr (le_antisymm huEI.2 (huE2 h))
        · exact Or.inl h.symm
      rcases hab2 with h | h
      · have hca : c + E = a := by rw [← hEeq]; exact h
        have hET'' : E = T := by linarith
        exact absurd hET''.symm (ne_of_lt hETlt)
      · have hcb : c + E = b := by rw [← hEeq]; exact h
        have hEbc : E = b - c := by linarith
        have hx0E : E ≤ x₀ := by rw [hEdef]; exact csInf_le hSbdd hx₀
        have hx0eq : x₀ = E := le_antisymm (by linarith [hx₀.1.2, hEbc]) hx0E
        exact hx₀.2 (by rw [← hx0eq] at huEI; exact huEI)
  · -- no bad point: `u` stays in the strip and the mean value theorem finishes
    have hSgood : ∀ x, x ∈ Set.Ioc T (b - c) → u x ∈ Set.Icc a b := by
      intro x hx
      by_contra hcon
      exact hS ⟨x, hx, hcon⟩
    intro ξ hξ
    rw [Set.mem_Icc] at hξ
    rcases eq_or_lt_of_le hξ.1 with h | h
    · rw [← h]; exact huT
    · have key : g ξ = 0 := by
        apply eq_zero_of_deriv_zero h hgT
        intro w hw
        rw [Set.mem_Icc] at hw
        rcases eq_or_lt_of_le hw.1 with h2 | h2
        · rw [← h2]; exact hderg T hTmem
        · exact hderg w (hSgood w ⟨h2, by linarith [hw.2, hξ.2]⟩)
      have : u ξ - (c + ξ) = 0 := by simpa only [hgdef] using key
      linarith

/-- **Right ray.** If `u t₀ = c + t₀` with `c + t₀ ∈ [a,b]`, then `u` follows the line `c + ·`
to the right of `t₀` for as long as that line stays in `[a,b]`. -/
private lemma right_ray {u : ℝ → ℝ} (hu : Continuous u) {a b c t₀ : ℝ}
    (h0 : u t₀ = c + t₀) (ha : a ≤ c + t₀) (hb : c + t₀ ≤ b)
    (hd : ∀ t, u t ∈ Set.Icc a b → HasDerivAt u 1 t) :
    ∀ s, t₀ ≤ s → c + s ∈ Set.Icc a b → u s = c + s := by
  -- the set of `x ≥ t₀` on which `u` is known to equal `c + ·` up to `x`
  set A : Set ℝ := {x | x ∈ Set.Icc t₀ (b - c) ∧ ∀ r ∈ Set.Icc t₀ x, u r = c + r} with hAdef
  have hZclosed : IsClosed {z | u z = c + z} := by
    have h1 : IsClosed ((fun z => u z - (c + z)) ⁻¹' {0}) :=
      isClosed_singleton.preimage (hu.sub (continuous_const.add continuous_id))
    convert h1 using 1
    ext z
    simp [sub_eq_zero]
  have ht₀A : t₀ ∈ A := by
    rw [hAdef]
    refine ⟨⟨le_refl _, by linarith⟩, ?_⟩
    intro r hr
    rw [Set.mem_Icc] at hr
    have : r = t₀ := le_antisymm hr.2 hr.1
    rw [this]; exact h0
  have hAne : A.Nonempty := ⟨t₀, ht₀A⟩
  have hAbdd : BddAbove A := ⟨b - c, fun x hx => by rw [hAdef] at hx; exact hx.1.2⟩
  set T := sSup A with hTdef
  have hmemA : T ∈ A := by
    rw [hAdef]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hTdef]; exact le_csSup hAbdd ht₀A
    · rw [hTdef]; exact csSup_le hAne (fun x hx => by rw [hAdef] at hx; exact hx.1.2)
    · intro r hr
      rw [Set.mem_Icc] at hr
      rcases lt_or_eq_of_le hr.2 with h | h
      · have h' : r < sSup A := by rw [← hTdef]; exact h
        obtain ⟨x, hxA, hxr⟩ := (lt_csSup_iff hAbdd hAne).mp h'
        rw [hAdef] at hxA
        exact hxA.2 r ⟨hr.1, le_of_lt hxr⟩
      · rw [h]
        have hAsp : A ⊆ {z | u z = c + z} := by
          intro x hx
          rw [hAdef] at hx
          exact hx.2 x ⟨hx.1.1, le_refl x⟩
        have hTcl : T ∈ closure {z | u z = c + z} := by
          rw [hTdef]
          exact closure_mono hAsp (csSup_mem_closure hAne hAbdd)
        rw [hZclosed.closure_eq] at hTcl
        exact hTcl
  have hTA : T ∈ Set.Icc t₀ (b - c) ∧ ∀ r ∈ Set.Icc t₀ T, u r = c + r := by
    have h := hmemA
    rw [hAdef] at h
    exact h
  have hTbc : T = b - c := by
    by_contra hne
    have hlt : T < b - c := lt_of_le_of_ne hTA.1.2 hne
    have huT : u T = c + T := hTA.2 T ⟨hTA.1.1, le_refl T⟩
    have ha' : a ≤ c + T := by linarith [hTA.1.1]
    have hext := extension_step hu huT ha' hlt hd
    have hbcA : b - c ∈ A := by
      rw [hAdef]
      refine ⟨⟨by linarith [hTA.1.1], le_refl _⟩, ?_⟩
      intro r hr
      rw [Set.mem_Icc] at hr
      rcases le_or_gt r T with h | h
      · exact hTA.2 r ⟨hr.1, h⟩
      · exact hext r ⟨le_of_lt h, hr.2⟩
    have : b - c ≤ T := by rw [hTdef]; exact le_csSup hAbdd hbcA
    linarith
  intro s hts hcs
  rw [Set.mem_Icc] at hcs
  refine hTA.2 s ⟨hts, ?_⟩
  rw [hTbc]; linarith [hcs.2]

/-- **Left ray**, obtained from `right_ray` by the reflection `t ↦ -t`. -/
private lemma left_ray {u : ℝ → ℝ} (hu : Continuous u) {a b c t₀ : ℝ}
    (h0 : u t₀ = c + t₀) (ha : a ≤ c + t₀) (hb : c + t₀ ≤ b)
    (hd : ∀ t, u t ∈ Set.Icc a b → HasDerivAt u 1 t) :
    ∀ s, s ≤ t₀ → c + s ∈ Set.Icc a b → u s = c + s := by
  have hUcont : Continuous (fun s : ℝ => -u (-s)) := (hu.comp continuous_neg).neg
  have hUd : ∀ t, (fun s : ℝ => -u (-s)) t ∈ Set.Icc (-b) (-a) →
      HasDerivAt (fun s : ℝ => -u (-s)) 1 t := by
    intro t ht
    have ht' : u (-t) ∈ Set.Icc a b := by
      rw [Set.mem_Icc] at ht ⊢
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h1 : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
    have h2 : HasDerivAt (fun s : ℝ => u (-s)) (1 * (-1)) t := (hd (-t) ht').comp t h1
    have h3 : HasDerivAt (fun s : ℝ => -(u (-s))) (-(1 * (-1))) t := h2.neg
    simpa using h3
  have hU0 : (fun s : ℝ => -u (-s)) (-t₀) = (-c) + (-t₀) := by
    show -u (-(-t₀)) = -c + -t₀
    rw [neg_neg, h0]
    ring
  have hUa : (-b) ≤ (-c) + (-t₀) := by linarith
  have hUb : (-c) + (-t₀) ≤ (-a) := by linarith
  have key := right_ray hUcont hU0 hUa hUb hUd
  intro s hs hcs
  have h1 : (-t₀) ≤ -s := by linarith
  have h2 : (-c) + (-s) ∈ Set.Icc (-b) (-a) := by
    rw [Set.mem_Icc] at hcs ⊢
    exact ⟨by linarith [hcs.2], by linarith [hcs.1]⟩
  have hkey := key (-s) h1 h2
  have hval : -u s = -c + -s := by simpa using hkey
  linarith

theorem eq_of_deriv_eq_one {u : ℝ → ℝ} (hu : Continuous u) (a b : ℝ)
    (h0 : u 0 ∈ Set.Icc a b)
    (hd : ∀ t, u t ∈ Set.Icc a b → HasDerivAt u 1 t) :
    ∀ t, u 0 + t ∈ Set.Icc a b → u t = u 0 + t := by
  intro t ht
  rw [Set.mem_Icc] at h0 ht
  rcases le_or_gt 0 t with h | h
  · exact right_ray hu (by ring : u 0 = u 0 + 0) (by linarith [h0.1]) (by linarith [h0.2]) hd t h ht
  · exact left_ray hu (by ring : u 0 = u 0 + 0) (by linarith [h0.1]) (by linarith [h0.2]) hd t (le_of_lt h) ht

end Work.Drive.N2
