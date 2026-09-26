import Mathlib

/-!
# Extending a homeomorphism of an arc in the circle to the whole circle

Two continuous maps `u v : ℝ → Circle` which are injective on `[-1,1]` (i.e. two embedded
closed arcs of the circle, with a parametrisation) differ by a homeomorphism of the circle:
`∃ g : Circle ≃ₜ Circle, ∀ t ∈ [-1,1], g (u t) = v t`.

The proof goes through the universal cover `ℝ → Circle = AddCircle (2π)`.  Both `u` and `v`
lift to continuous `a b : ℝ → ℝ` agreeing with `u`, `v` on `[-1,1]`; the lifts are strictly
monotone there, and one builds explicitly a homeomorphism `G₀` of a fundamental interval
`[a(-1), a(-1) + 2π]`, interpolating the map `b ∘ a⁻¹` on the arc and an affine map on the
complementary arc, and descends it to `AddCircle (2π)` by `AddCircle.liftIco`.
-/

namespace Work.Drive.Mono

open Set

noncomputable section

/-- **A continuous injection on an interval inverts continuously.**  If `f` is continuous and
strictly monotone on `[-1,1]`, there is a continuous `g` with `g (f t) = t` for `t ∈ [-1,1]` and
`f (g x) = x` for `x` in the image interval. -/
private theorem exists_inv_of_strictMono {f : ℝ → ℝ} (hf : Continuous f)
    (hmono : StrictMonoOn f (Icc (-1 : ℝ) 1)) :
    ∃ g : ℝ → ℝ, Continuous g ∧ (∀ x, g x ∈ Icc (-1:ℝ) 1) ∧
      (∀ t ∈ Icc (-1:ℝ) 1, g (f t) = t) ∧
      (∀ x ∈ Icc (f (-1)) (f 1), f (g x) = x) := by
  have hle : f (-1) ≤ f 1 :=
    (hmono (left_mem_Icc.mpr (by norm_num)) (right_mem_Icc.mpr (by norm_num)) (by norm_num)).le
  have himg : f '' Icc (-1:ℝ) 1 = Icc (f (-1)) (f 1) :=
    ContinuousOn.image_Icc_of_monotoneOn (by norm_num) hf.continuousOn hmono.monotoneOn
  have hmem : ∀ t ∈ Icc (-1:ℝ) 1, f t ∈ Icc (f (-1)) (f 1) := by
    intro t ht; rw [← himg]; exact ⟨t, ht, rfl⟩
  let φ : ↥(Icc (-1:ℝ) 1) → ↥(Icc (f (-1)) (f 1)) := fun t => ⟨f t, hmem t t.2⟩
  have hφcont : Continuous φ :=
    Continuous.subtype_mk (hf.comp continuous_subtype_val) (fun t => hmem t t.2)
  have hφinj : Function.Injective φ := fun s t h =>
    Subtype.ext (hmono.injOn s.2 t.2 (congrArg Subtype.val h))
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← himg] at hy
    obtain ⟨t, ht, hty⟩ := hy
    exact ⟨⟨t, ht⟩, Subtype.ext hty⟩
  let e : ↥(Icc (-1:ℝ) 1) ≃ₜ ↥(Icc (f (-1)) (f 1)) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩) hφcont
  have he : ∀ t : ↥(Icc (-1:ℝ) 1), ((e t : ↥(Icc (f (-1)) (f 1))) : ℝ) = f t := fun t => rfl
  refine ⟨fun x => ((e.symm (Set.projIcc (f (-1)) (f 1) hle x) : ↥(Icc (-1:ℝ) 1)) : ℝ),
    (continuous_subtype_val.comp (e.symm.continuous.comp continuous_projIcc)), ?_, ?_, ?_⟩
  · intro x; exact (e.symm (Set.projIcc (f (-1)) (f 1) hle x)).2
  · intro t ht
    have hproj : Set.projIcc (f (-1)) (f 1) hle (f t) = ⟨f t, hmem t ht⟩ :=
      Set.projIcc_of_mem hle (hmem t ht)
    have h1 : e.symm (⟨f t, hmem t ht⟩ : ↥(Icc (f (-1)) (f 1))) = ⟨t, ht⟩ := by
      rw [Homeomorph.symm_apply_eq]; exact Subtype.ext rfl
    show ((e.symm (Set.projIcc (f (-1)) (f 1) hle (f t)) : ↥(Icc (-1:ℝ) 1)) : ℝ) = t
    rw [hproj, h1]
  · intro x hx
    have hproj : Set.projIcc (f (-1)) (f 1) hle x = ⟨x, hx⟩ := Set.projIcc_of_mem hle hx
    show f ((e.symm (Set.projIcc (f (-1)) (f 1) hle x) : ↥(Icc (-1:ℝ) 1)) : ℝ) = x
    rw [hproj, ← he (e.symm ⟨x, hx⟩), Homeomorph.apply_symm_apply]

/-- The `Circle.exp`-lift of a continuous map into the circle that is injective on `[-1,1]`
spans less than the period `2π`. -/
private theorem span_lt_of_injOn {P : ℝ} (hP : 0 < P) {U : ℝ → AddCircle P} {a : ℝ → ℝ}
    (ha : Continuous a) (hU : InjOn U (Icc (-1:ℝ) 1))
    (hA : ∀ t ∈ Icc (-1:ℝ) 1, (a t : AddCircle P) = U t) :
    a 1 - a (-1) < P := by
  by_contra h
  push Not at h
  have hmem : a (-1) + P ∈ Icc (a (-1)) (a 1) := ⟨by linarith, by linarith⟩
  obtain ⟨s, hs, hsa⟩ :=
    intermediate_value_Icc (by norm_num : (-1:ℝ) ≤ 1) ha.continuousOn hmem
  have hcls : (a s : AddCircle P) = (a (-1) : AddCircle P) := by
    rw [hsa, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  have hUt : U s = U (-1) := by
    rw [← hA s hs, ← hA (-1) (left_mem_Icc.mpr (by norm_num)), hcls]
  have hsinj := hU hs (left_mem_Icc.mpr (by norm_num)) hUt
  subst hsinj
  linarith

/-- **The core of the extension theorem.**  Two strictly increasing continuous maps `a`, `b` of
`[-1,1]` whose spans are smaller than the period `P`: there is a homeomorphism of `AddCircle P`
carrying the class of `a t` to the class of `b t`.  The homeomorphism is built from the map
`b ∘ a⁻¹` on the image of `a`, extended over the complementary arc by an affine map. -/
private theorem core_addCircle {P : ℝ} (hP : 0 < P)
    {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (ham : StrictMonoOn a (Icc (-1:ℝ) 1)) (hbm : StrictMonoOn b (Icc (-1:ℝ) 1))
    (hspanA : a 1 - a (-1) < P) (hspanB : b 1 - b (-1) < P) :
    ∃ g : AddCircle P ≃ₜ AddCircle P,
      ∀ t ∈ Icc (-1:ℝ) 1, g (a t : AddCircle P) = (b t : AddCircle P) := by
  haveI : Fact (0 < P) := ⟨hP⟩
  obtain ⟨Ainv, hAcont, hAmem, hAleft, hAright⟩ := exists_inv_of_strictMono ha ham
  obtain ⟨Binv, hBcont, hBmem, hBleft, hBright⟩ := exists_inv_of_strictMono hb hbm
  have hlt_a : a (-1) < a 1 :=
    ham (left_mem_Icc.mpr (by norm_num)) (right_mem_Icc.mpr (by norm_num)) (by norm_num)
  have hlt_b : b (-1) < b 1 :=
    hbm (left_mem_Icc.mpr (by norm_num)) (right_mem_Icc.mpr (by norm_num)) (by norm_num)
  set L : ℝ := a 1 - a (-1) with hL
  set S : ℝ := b 1 - b (-1) with hS
  have hPL : P - L ≠ 0 := by rw [hL]; linarith
  have hPS : P - S ≠ 0 := by rw [hS]; linarith
  have hPLpos : 0 < P - L := by rw [hL]; linarith
  have hPSpos : 0 < P - S := by rw [hS]; linarith
  -- the map on the arc and the affine map on the complementary arc
  let H : ℝ → ℝ := fun x => b (Ainv x)
  let Hinv : ℝ → ℝ := fun y => a (Binv y)
  let ψ : ℝ → ℝ := fun x => b 1 + (x - a 1) * ((P - S) / (P - L))
  let ψinv : ℝ → ℝ := fun y => a 1 + (y - b 1) * ((P - L) / (P - S))
  have hHcont : Continuous H := by
    show Continuous (fun x => b (Ainv x)); exact hb.comp hAcont
  have hHinv_cont : Continuous Hinv := by
    show Continuous (fun y => a (Binv y)); exact ha.comp hBcont
  have hψ_cont : Continuous ψ := by
    show Continuous (fun x => b 1 + (x - a 1) * ((P - S)/(P - L))); fun_prop
  have hψinv_cont : Continuous ψinv := by
    show Continuous (fun y => a 1 + (y - b 1) * ((P - L)/(P - S))); fun_prop
  have hH_a : ∀ t ∈ Icc (-1:ℝ) 1, H (a t) = b t := by
    intro t ht; show b (Ainv (a t)) = b t; rw [hAleft t ht]
  have hHinv_b : ∀ t ∈ Icc (-1:ℝ) 1, Hinv (b t) = a t := by
    intro t ht; show a (Binv (b t)) = a t; rw [hBleft t ht]
  have hH_mem : ∀ x ∈ Icc (a (-1)) (a 1), H x ∈ Icc (b (-1)) (b 1) := by
    intro x hx
    have h1 : Ainv x ∈ Icc (-1:ℝ) 1 := hAmem x
    show b (Ainv x) ∈ Icc (b (-1)) (b 1)
    exact ⟨hbm.monotoneOn (left_mem_Icc.mpr (by norm_num)) h1 h1.1,
           hbm.monotoneOn h1 (right_mem_Icc.mpr (by norm_num)) h1.2⟩
  have hHinv_mem : ∀ y ∈ Icc (b (-1)) (b 1), Hinv y ∈ Icc (a (-1)) (a 1) := by
    intro y hy
    have h1 : Binv y ∈ Icc (-1:ℝ) 1 := hBmem y
    show a (Binv y) ∈ Icc (a (-1)) (a 1)
    exact ⟨ham.monotoneOn (left_mem_Icc.mpr (by norm_num)) h1 h1.1,
           ham.monotoneOn h1 (right_mem_Icc.mpr (by norm_num)) h1.2⟩
  have hHinv_H : ∀ x ∈ Icc (a (-1)) (a 1), Hinv (H x) = x := by
    intro x hx
    show a (Binv (b (Ainv x))) = x
    rw [hBleft (Ainv x) (hAmem x), hAright x hx]
  have hH_Hinv : ∀ y ∈ Icc (b (-1)) (b 1), H (Hinv y) = y := by
    intro y hy
    show b (Ainv (a (Binv y))) = y
    rw [hAleft (Binv y) (hBmem y), hBright y hy]
  have hψ_a1 : ψ (a 1) = b 1 := by show b 1 + (a 1 - a 1) * _ = b 1; ring
  have hψ_inv : ∀ x, ψinv (ψ x) = x := by
    intro x
    show a 1 + (ψ x - b 1) * ((P - L)/(P - S)) = x
    rw [show ψ x = b 1 + (x - a 1) * ((P - S)/(P - L)) from rfl]
    field_simp
    ring
  have hψ_ψinv : ∀ y, ψ (ψinv y) = y := by
    intro y
    show b 1 + (ψinv y - a 1) * ((P - S)/(P - L)) = y
    rw [show ψinv y = a 1 + (y - b 1) * ((P - L)/(P - S)) from rfl]
    field_simp
    ring
  have hψ_mono : Monotone ψ := by
    intro x y hxy
    show b 1 + (x - a 1) * ((P - S)/(P - L)) ≤ b 1 + (y - a 1) * ((P - S)/(P - L))
    have h : 0 ≤ (P - S)/(P - L) := le_of_lt (div_pos hPSpos hPLpos)
    have h2 : x - a 1 ≤ y - a 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h2 h]
  have hψinv_mono : Monotone ψinv := by
    intro x y hxy
    show a 1 + (x - b 1) * ((P - L)/(P - S)) ≤ a 1 + (y - b 1) * ((P - L)/(P - S))
    have h : 0 ≤ (P - L)/(P - S) := le_of_lt (div_pos hPLpos hPSpos)
    have h2 : x - b 1 ≤ y - b 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h2 h]
  have hψ_end : ψ (a (-1) + P) = b (-1) + P := by
    show b 1 + (a (-1) + P - a 1) * ((P - S)/(P - L)) = b (-1) + P
    rw [show a (-1) + P - a 1 = P - L by rw [hL]; ring,
        show b 1 = b (-1) + S by rw [hS]; ring]
    field_simp
    ring
  have hψinv_end : ψinv (b (-1) + P) = a (-1) + P := by
    show a 1 + (b (-1) + P - b 1) * ((P - L)/(P - S)) = a (-1) + P
    rw [show b (-1) + P - b 1 = P - S by rw [hS]; ring,
        show a 1 = a (-1) + L by rw [hL]; ring]
    field_simp
    ring
  have hψinv_b1 : ψinv (b 1) = a 1 := by
    show a 1 + (b 1 - b 1) * ((P - L)/(P - S)) = a 1
    ring
  -- glue the two pieces
  let G₀ : ℝ → ℝ := fun x => if x ≤ a 1 then H x else ψ x
  let G₁ : ℝ → ℝ := fun y => if y ≤ b 1 then Hinv y else ψinv y
  have hG0_le : ∀ x, x ≤ a 1 → G₀ x = H x := by
    intro x hx; show (if x ≤ a 1 then H x else ψ x) = H x; rw [if_pos hx]
  have hG0_ge : ∀ x, a 1 ≤ x → G₀ x = ψ x := by
    intro x hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · show (if x ≤ a 1 then H x else ψ x) = ψ x
      rw [if_neg (not_le.mpr hlt)]
    · rw [← heq, hG0_le (a 1) le_rfl,
        hH_a 1 (right_mem_Icc.mpr (by norm_num)), hψ_a1]
  have hG1_le : ∀ y, y ≤ b 1 → G₁ y = Hinv y := by
    intro y hy; show (if y ≤ b 1 then Hinv y else ψinv y) = Hinv y; rw [if_pos hy]
  have hG1_ge : ∀ y, b 1 ≤ y → G₁ y = ψinv y := by
    intro y hy
    rcases lt_or_eq_of_le hy with hlt | heq
    · show (if y ≤ b 1 then Hinv y else ψinv y) = ψinv y
      rw [if_neg (not_le.mpr hlt)]
    · rw [← heq, hG1_le (b 1) le_rfl]
      show a (Binv (b 1)) = ψinv (b 1)
      rw [hBleft 1 (right_mem_Icc.mpr (by norm_num)), hψinv_b1]
  have hG0_start : G₀ (a (-1)) = b (-1) := by
    rw [hG0_le (a (-1)) (le_of_lt hlt_a), hH_a (-1) (left_mem_Icc.mpr (by norm_num))]
  have hG0_end : G₀ (a (-1) + P) = b (-1) + P := by
    rw [hG0_ge (a (-1) + P) (by linarith), hψ_end]
  have hG1_start : G₁ (b (-1)) = a (-1) := by
    rw [hG1_le (b (-1)) (le_of_lt hlt_b), hHinv_b (-1) (left_mem_Icc.mpr (by norm_num))]
  have hG1_end : G₁ (b (-1) + P) = a (-1) + P := by
    rw [hG1_ge (b (-1) + P) (by linarith), hψinv_end]
  have hG0_mem : ∀ x ∈ Icc (a (-1)) (a (-1) + P), G₀ x ∈ Icc (b (-1)) (b (-1) + P) := by
    intro x hx
    rcases le_or_gt x (a 1) with hxl | hxg
    · rw [hG0_le x hxl]
      have h := hH_mem x ⟨hx.1, hxl⟩
      exact ⟨h.1, le_trans h.2 (by linarith [hS, hspanB])⟩
    · rw [hG0_ge x hxg.le]
      have h1 : ψ (a 1) ≤ ψ x := hψ_mono (le_of_lt hxg)
      have h2 : ψ x ≤ ψ (a (-1) + P) := hψ_mono hx.2
      rw [hψ_a1] at h1
      rw [hψ_end] at h2
      exact ⟨le_trans (le_of_lt hlt_b) h1, h2⟩
  have hG1_mem : ∀ y ∈ Icc (b (-1)) (b (-1) + P), G₁ y ∈ Icc (a (-1)) (a (-1) + P) := by
    intro y hy
    rcases le_or_gt y (b 1) with hyl | hyg
    · rw [hG1_le y hyl]
      have h := hHinv_mem y ⟨hy.1, hyl⟩
      exact ⟨h.1, le_trans h.2 (by linarith [hL, hspanA])⟩
    · rw [hG1_ge y hyg.le]
      have h1 : ψinv (b 1) ≤ ψinv y := hψinv_mono (le_of_lt hyg)
      have h2 : ψinv y ≤ ψinv (b (-1) + P) := hψinv_mono hy.2
      rw [hψinv_b1] at h1
      rw [hψinv_end] at h2
      exact ⟨le_trans (le_of_lt hlt_a) h1, h2⟩
  have hG0_cont : Continuous G₀ := by
    show Continuous (fun x => if x ≤ a 1 then H x else ψ x)
    refine continuous_if_le continuous_id continuous_const ?_ ?_ ?_
    · exact hHcont.continuousOn.mono (subset_univ _)
    · exact hψ_cont.continuousOn.mono (subset_univ _)
    · intro x hx
      rw [hx, hH_a 1 (right_mem_Icc.mpr (by norm_num)), hψ_a1]
  have hG1_cont : Continuous G₁ := by
    show Continuous (fun y => if y ≤ b 1 then Hinv y else ψinv y)
    refine continuous_if_le continuous_id continuous_const ?_ ?_ ?_
    · exact hHinv_cont.continuousOn.mono (subset_univ _)
    · exact hψinv_cont.continuousOn.mono (subset_univ _)
    · intro y hy
      rw [hy]
      show a (Binv (b 1)) = ψinv (b 1)
      rw [hBleft 1 (right_mem_Icc.mpr (by norm_num)), hψinv_b1]
  have hG1G0 : ∀ x ∈ Icc (a (-1)) (a (-1) + P), G₁ (G₀ x) = x := by
    intro x hx
    rcases le_or_gt x (a 1) with hxl | hxg
    · rw [hG0_le x hxl]
      have hmem := hH_mem x ⟨hx.1, hxl⟩
      rw [hG1_le (H x) hmem.2, hHinv_H x ⟨hx.1, hxl⟩]
    · rw [hG0_ge x hxg.le]
      have hmem : b 1 ≤ ψ x := by
        have h := hψ_mono hxg.le
        rwa [hψ_a1] at h
      rw [hG1_ge (ψ x) hmem, hψ_inv x]
  have hG0G1 : ∀ y ∈ Icc (b (-1)) (b (-1) + P), G₀ (G₁ y) = y := by
    intro y hy
    rcases le_or_gt y (b 1) with hyl | hyg
    · rw [hG1_le y hyl]
      have hmem := hHinv_mem y ⟨hy.1, hyl⟩
      rw [hG0_le (Hinv y) hmem.2, hH_Hinv y ⟨hy.1, hyl⟩]
    · rw [hG1_ge y hyg.le]
      have hmem : a 1 ≤ ψinv y := by
        have h := hψinv_mono hyg.le
        rwa [hψinv_b1] at h
      rw [hG0_ge (ψinv y) hmem, hψ_ψinv y]
  -- descend to `AddCircle P`
  let F : ℝ → AddCircle P := fun x => (G₀ x : AddCircle P)
  let F' : ℝ → AddCircle P := fun y => (G₁ y : AddCircle P)
  have hFcont : ContinuousOn F (Icc (a (-1)) (a (-1) + P)) :=
    (AddCircle.continuous_mk' P).comp_continuousOn hG0_cont.continuousOn
  have hFcont' : ContinuousOn F' (Icc (b (-1)) (b (-1) + P)) :=
    (AddCircle.continuous_mk' P).comp_continuousOn hG1_cont.continuousOn
  have hFP : F (a (-1)) = F (a (-1) + P) := by
    show (G₀ (a (-1)) : AddCircle P) = (G₀ (a (-1) + P) : AddCircle P)
    rw [hG0_start, hG0_end, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  have hF'P : F' (b (-1)) = F' (b (-1) + P) := by
    show (G₁ (b (-1)) : AddCircle P) = (G₁ (b (-1) + P) : AddCircle P)
    rw [hG1_start, hG1_end, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  let g : AddCircle P → AddCircle P := AddCircle.liftIco P (a (-1)) F
  let h : AddCircle P → AddCircle P := AddCircle.liftIco P (b (-1)) F'
  have hg_cont : Continuous g := AddCircle.liftIco_continuous hFP hFcont
  have hh_cont : Continuous h := AddCircle.liftIco_continuous hF'P hFcont'
  have g_apply : ∀ x ∈ Icc (a (-1)) (a (-1) + P),
      g (x : AddCircle P) = (G₀ x : AddCircle P) := by
    intro x hx
    rcases lt_or_eq_of_le hx.2 with hlt | heq
    · rw [show g (x : AddCircle P) = F x from
        AddCircle.liftIco_coe_apply (f := F) ⟨hx.1, hlt⟩]
    · rw [heq, AddCircle.coe_add_period]
      rw [show g (((a (-1) : ℝ)) : AddCircle P) = F (a (-1)) from
        AddCircle.liftIco_coe_apply (f := F) ⟨le_refl _, by linarith [hP]⟩]
      exact hFP
  have h_apply : ∀ y ∈ Icc (b (-1)) (b (-1) + P),
      h (y : AddCircle P) = (G₁ y : AddCircle P) := by
    intro y hy
    rcases lt_or_eq_of_le hy.2 with hlt | heq
    · rw [show h (y : AddCircle P) = F' y from
        AddCircle.liftIco_coe_apply (f := F') ⟨hy.1, hlt⟩]
    · rw [heq, AddCircle.coe_add_period]
      rw [show h (((b (-1) : ℝ)) : AddCircle P) = F' (b (-1)) from
        AddCircle.liftIco_coe_apply (f := F') ⟨le_refl _, by linarith [hP]⟩]
      exact hF'P
  have hg1 : ∀ z, h (g z) = z := by
    intro z
    set x : ℝ := ((AddCircle.equivIco P (a (-1))) z : ℝ) with hx
    have hxmem : x ∈ Ico (a (-1)) (a (-1) + P) := ((AddCircle.equivIco P (a (-1))) z).2
    have hxz : (x : AddCircle P) = z := AddCircle.coe_equivIco
    rw [← hxz, g_apply x ⟨hxmem.1, hxmem.2.le⟩,
      h_apply (G₀ x) (hG0_mem x ⟨hxmem.1, hxmem.2.le⟩),
      hG1G0 x ⟨hxmem.1, hxmem.2.le⟩, hxz]
  have hg2 : ∀ z, g (h z) = z := by
    intro z
    set y : ℝ := ((AddCircle.equivIco P (b (-1))) z : ℝ) with hy
    have hymem : y ∈ Ico (b (-1)) (b (-1) + P) := ((AddCircle.equivIco P (b (-1))) z).2
    have hyz : (y : AddCircle P) = z := AddCircle.coe_equivIco
    rw [← hyz, h_apply y ⟨hymem.1, hymem.2.le⟩,
      g_apply (G₁ y) (hG1_mem y ⟨hymem.1, hymem.2.le⟩),
      hG0G1 y ⟨hymem.1, hymem.2.le⟩, hyz]
  have hgfin : ∀ t ∈ Icc (-1:ℝ) 1, g (a t : AddCircle P) = (b t : AddCircle P) := by
    intro t ht
    have hat : a t ∈ Icc (a (-1)) (a (-1) + P) := by
      refine ⟨ham.monotoneOn (left_mem_Icc.mpr (by norm_num)) ht ht.1, ?_⟩
      have h1 := ham.monotoneOn ht (right_mem_Icc.mpr (by norm_num)) ht.2
      linarith [hL, hspanA]
    rw [g_apply (a t) hat,
      hG0_le (a t) (ham.monotoneOn ht (right_mem_Icc.mpr (by norm_num)) ht.2)]
    exact congrArg (fun z : ℝ => (z : AddCircle P)) (hH_a t ht)
  let G : AddCircle P ≃ₜ AddCircle P :=
    ⟨(⟨g, h, hg1, hg2⟩ : AddCircle P ≃ AddCircle P), hg_cont, hh_cont⟩
  exact ⟨G, fun t ht => hgfin t ht⟩

/-- The same as `core_addCircle`, but with only the classes of the lifts available, and the
monotonicity of `a` assumed; the monotonicity of `b` is dealt with by negating the circle. -/
private theorem core_T_inc {P : ℝ} (hP : 0 < P) {U V : ℝ → AddCircle P}
    (hU : Continuous U) (hV : Continuous V)
    (hUi : InjOn U (Icc (-1:ℝ) 1)) (hVi : InjOn V (Icc (-1:ℝ) 1))
    {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hA : ∀ t ∈ Icc (-1:ℝ) 1, (a t : AddCircle P) = U t)
    (hB : ∀ t ∈ Icc (-1:ℝ) 1, (b t : AddCircle P) = V t)
    (ham : StrictMonoOn a (Icc (-1:ℝ) 1)) :
    ∃ g : AddCircle P ≃ₜ AddCircle P, ∀ t ∈ Icc (-1:ℝ) 1, g (U t) = V t := by
  have hbi : InjOn b (Icc (-1:ℝ) 1) := fun s hs t ht h =>
    hVi hs ht (by rw [← hB s hs, ← hB t ht, h])
  have hspanA : a 1 - a (-1) < P := span_lt_of_injOn hP ha hUi hA
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc' (by norm_num) hb.continuousOn hbi with hbm | hbn
  · have hspanB : b 1 - b (-1) < P := span_lt_of_injOn hP hb hVi hB
    obtain ⟨g, hg⟩ := core_addCircle hP ha hb ham hbm hspanA hspanB
    exact ⟨g, fun t ht => by rw [← hA t ht, ← hB t ht]; exact hg t ht⟩
  · -- `b` is decreasing: use `-b`, which lifts `-V`
    have hb'cont : Continuous (fun t => -(b t)) := hb.neg
    have hb'mon : StrictMonoOn (fun t => -(b t)) (Icc (-1:ℝ) 1) := by
      intro s hs t ht hst
      exact neg_lt_neg (hbn hs ht hst)
    have hb'eq : ∀ t ∈ Icc (-1:ℝ) 1,
        ((-(b t)) : AddCircle P) = Homeomorph.neg (AddCircle P) (V t) := by
      intro t ht
      rw [← hB t ht]
      show ((-(b t)) : AddCircle P) = - ((b t : ℝ) : AddCircle P)
      rfl
    have hspanB' : (-(b 1)) - (-(b (-1))) < P := by
      have hVi' : InjOn (fun t => Homeomorph.neg (AddCircle P) (V t)) (Icc (-1:ℝ) 1) :=
        fun s hs t ht h => hVi hs ht ((Homeomorph.neg (AddCircle P)).injective h)
      exact span_lt_of_injOn hP hb'cont hVi' hb'eq
    obtain ⟨g, hg⟩ := core_addCircle hP ha hb'cont ham hb'mon hspanA hspanB'
    refine ⟨g.trans (Homeomorph.neg (AddCircle P)), fun t ht => ?_⟩
    have h1 : g (U t) = (((-(b t)) : ℝ) : AddCircle P) := by rw [← hA t ht, hg t ht]
    rw [Homeomorph.trans_apply, h1]
    show - ((((-(b t)) : ℝ)) : AddCircle P) = V t
    simp [hB t ht]

/-- Any two continuous lifts of continuous maps into `AddCircle P`, injective on `[-1,1]`, differ
by a homeomorphism of `AddCircle P` taking one to the other on `[-1,1]`. -/
private theorem core_T {P : ℝ} (hP : 0 < P) {U V : ℝ → AddCircle P}
    (hU : Continuous U) (hV : Continuous V)
    (hUi : InjOn U (Icc (-1:ℝ) 1)) (hVi : InjOn V (Icc (-1:ℝ) 1))
    {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hA : ∀ t ∈ Icc (-1:ℝ) 1, (a t : AddCircle P) = U t)
    (hB : ∀ t ∈ Icc (-1:ℝ) 1, (b t : AddCircle P) = V t) :
    ∃ g : AddCircle P ≃ₜ AddCircle P, ∀ t ∈ Icc (-1:ℝ) 1, g (U t) = V t := by
  have hai : InjOn a (Icc (-1:ℝ) 1) := fun s hs t ht h =>
    hUi hs ht (by rw [← hA s hs, ← hA t ht, h])
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc' (by norm_num) ha.continuousOn hai with ham | han
  · exact core_T_inc hP hU hV hUi hVi ha hb hA hB ham
  · -- `a` is decreasing: reflect the parameter
    have hU'inj : InjOn (fun t => U (-t)) (Icc (-1:ℝ) 1) := by
      intro s hs t ht h
      have h1 : -s ∈ Icc (-1:ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have h2 : -t ∈ Icc (-1:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have := hUi h1 h2 h
      linarith
    have hV'inj : InjOn (fun t => V (-t)) (Icc (-1:ℝ) 1) := by
      intro s hs t ht h
      have h1 : -s ∈ Icc (-1:ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have h2 : -t ∈ Icc (-1:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have := hVi h1 h2 h
      linarith
    have hA' : ∀ t ∈ Icc (-1:ℝ) 1, ((a (-t)) : AddCircle P) = U (-t) := by
      intro t ht
      exact hA (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hB' : ∀ t ∈ Icc (-1:ℝ) 1, ((b (-t)) : AddCircle P) = V (-t) := by
      intro t ht
      exact hB (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have ham' : StrictMonoOn (fun t => a (-t)) (Icc (-1:ℝ) 1) := by
      intro s hs t ht hst
      have h1 : -t ∈ Icc (-1:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have h2 : -s ∈ Icc (-1:ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      exact han h1 h2 (neg_lt_neg hst)
    obtain ⟨g, hg⟩ := core_T_inc hP (hU.comp continuous_neg) (hV.comp continuous_neg)
      hU'inj hV'inj (ha.comp continuous_neg) (hb.comp continuous_neg) hA' hB' ham'
    refine ⟨g, fun t ht => ?_⟩
    have ht' : -t ∈ Icc (-1:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa using hg (-t) ht'

/-- A continuous map into the unit circle has a continuous lift to `ℝ` along `Circle.exp`. -/
private theorem exists_lift_exp (c : ℝ → Circle) (hc : Continuous c) :
    ∃ a : ℝ → ℝ, Continuous a ∧ ∀ t ∈ Icc (-1 : ℝ) 1, Circle.exp (a t) = c t := by
  obtain ⟨e₀, he₀⟩ := Circle.exp_surjective (c (-1))
  let γ : C(unitInterval, Circle) :=
    ⟨fun s => c (-1 + 2 * (s : ℝ)), hc.comp (by fun_prop)⟩
  have hγ0 : γ 0 = Circle.exp e₀ := by
    show c (-1 + 2 * ((0 : unitInterval) : ℝ)) = Circle.exp e₀
    rw [he₀]
    norm_num
  let Γ := Circle.isCoveringMap_exp.liftPath γ e₀ hγ0
  have hΓ : ∀ s : unitInterval, Circle.exp (Γ s) = γ s :=
    fun s => congr_fun (IsCoveringMap.liftPath_lifts Circle.isCoveringMap_exp γ e₀ hγ0) s
  refine ⟨fun t => Γ (Set.projIcc 0 1 (by norm_num) ((t + 1) / 2)), ?_, ?_⟩
  · exact Γ.continuous.comp (continuous_projIcc.comp (by fun_prop))
  · intro t ht
    have ht' : (t + 1) / 2 ∈ Icc (0:ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hproj : Set.projIcc 0 1 (by norm_num) ((t+1)/2) = ⟨(t+1)/2, ht'⟩ :=
      Set.projIcc_of_mem _ ht'
    calc Circle.exp (Γ (Set.projIcc 0 1 (by norm_num) ((t + 1) / 2)))
        = γ (Set.projIcc 0 1 (by norm_num) ((t + 1) / 2)) := hΓ _
      _ = γ ⟨(t+1)/2, ht'⟩ := by rw [hproj]
      _ = c t := by
          show c (-1 + 2 * ((t+1)/2 : ℝ)) = c t
          ring_nf

theorem sphereArc_extension {u v : ℝ → Metric.sphere (0 : ℂ) 1}
    (hu : Continuous u) (hv : Continuous v)
    (hui : Set.InjOn u (Set.Icc (-1 : ℝ) 1)) (hvi : Set.InjOn v (Set.Icc (-1 : ℝ) 1)) :
    ∃ g : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1,
      ∀ t ∈ Set.Icc (-1 : ℝ) 1, g (u t) = v t := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  obtain ⟨a, ha, hae⟩ := exists_lift_exp (c := fun t => (u t : Circle)) hu
  obtain ⟨b, hb, hbe⟩ := exists_lift_exp (c := fun t => (v t : Circle)) hv
  -- transport the problem to `AddCircle (2 * π)`
  let e : AddCircle (2 * Real.pi) ≃ₜ Circle := AddCircle.homeomorphCircle'
  let U : ℝ → AddCircle (2 * Real.pi) := fun t => e.symm ((u t : Circle))
  let V : ℝ → AddCircle (2 * Real.pi) := fun t => e.symm ((v t : Circle))
  have hU : Continuous U := by
    show Continuous (fun t => e.symm ((u t : Circle)))
    exact e.symm.continuous.comp hu
  have hV : Continuous V := by
    show Continuous (fun t => e.symm ((v t : Circle)))
    exact e.symm.continuous.comp hv
  have hUi : InjOn U (Icc (-1:ℝ) 1) := by
    intro s hs t ht h
    have h1 : (u s : Circle) = (u t : Circle) := e.symm.injective h
    exact hui hs ht h1
  have hVi : InjOn V (Icc (-1:ℝ) 1) := by
    intro s hs t ht h
    have h1 : (v s : Circle) = (v t : Circle) := e.symm.injective h
    exact hvi hs ht h1
  have hA : ∀ t ∈ Icc (-1:ℝ) 1, ((a t) : AddCircle (2 * Real.pi)) = U t := by
    intro t ht
    have h1 : e ((a t) : AddCircle (2 * Real.pi)) = (u t : Circle) := by
      rw [AddCircle.homeomorphCircle'_apply_mk]
      exact hae t ht
    show ((a t) : AddCircle (2 * Real.pi)) = e.symm ((u t : Circle))
    rw [← h1, Homeomorph.symm_apply_apply]
  have hB : ∀ t ∈ Icc (-1:ℝ) 1, ((b t) : AddCircle (2 * Real.pi)) = V t := by
    intro t ht
    have h1 : e ((b t) : AddCircle (2 * Real.pi)) = (v t : Circle) := by
      rw [AddCircle.homeomorphCircle'_apply_mk]
      exact hbe t ht
    show ((b t) : AddCircle (2 * Real.pi)) = e.symm ((v t : Circle))
    rw [← h1, Homeomorph.symm_apply_apply]
  obtain ⟨g, hg⟩ := core_T (P := 2 * Real.pi) (by positivity) hU hV hUi hVi ha hb hA hB
  refine ⟨(e.symm.trans g).trans e, fun t ht => ?_⟩
  show e (g (e.symm ((u t : Circle)))) = v t
  rw [hg t ht]
  exact e.apply_symm_apply ((v t : Circle))

end

end Work.Drive.Mono
