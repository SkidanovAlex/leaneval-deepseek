/-
  WilC4/rexp_deep_window_value_ratio_aux : auxiliary lemmas for the proof of
  `Work.WilC4.rexp_deep_window_value_ratio` (kept in a separate module because of the workspace file
  size limit).

  The mathematical content of the main proof is: the fibre of a definable family has, by
  `ulpm_mono_param`, only `N₁` monotonicity breakpoints per fibre, so on a wide window it has
  `N₁ + 1` monotone slots; the doubling ratio is monotone on the window (`ULPMStruct`); the
  telescoping identity `G (2x) = ρ x · G x` then shows that the *value* ratio over `(z, z')` is
  bounded by the value ratio over a *shifted* pair whose slot is breakpoint free; on such a slot the
  deep-ratio bound `deep_ratio_scale_bdd` gives the bound.

  The lemmas here are pure real analysis plus the fibre dictionary (`valY`, `ratioY`, `RatW`):

  * `free_cont`, `free_sign`, `free_ratioY_pos` : continuity, constant sign and positivity of the
    doubling ratio on an interval free of `B₀`;
  * `ratioY_monoOrAnti` : the doubling ratio is monotone-or-antitone on the part of a free window
    on which the double is still in the window;
  * `slot_monoOrAnti` : the fibre is monotone-or-antitone on a closed slot free of the breakpoint
    family `Bm`;
  * `abs_le_of_slot_mono` : the value bound on a monotone slot;
  * `telescoping_up`, `telescoping_down`, `prod_le_prod_of_le`, `rise_le_shift_up`,
    `rise_le_shift_down` : the shift (telescoping) estimates;
  * `exists_free_slot` : the pigeonhole that produces a breakpoint-free slot.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ULPMDefs
import Submission.Work.WilC4.ErealDefs
import Submission.Work.WilC4.deep_ratio_scale_bdd
import Submission.Work.WilC4.ULPMAsm
import Submission.Work.WilC4.monoOn_Icc_of_Ioo
import Submission.Work.WilC4.mono_of_three_point
import Submission.Work.WilC4.encardLePigeonhole
import Submission.Work.WilC4.ulpm_mono_param

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC4.Route (Gr valY ratioY valY_mem InD eq_valY)

variable {k : ℕ}

/-- `min a c ≤ b ≤ max a c` implies `|b| ≤ max |a| |c|`. -/
private theorem abs_le_max_abs_of_between {a b c : ℝ} (h1 : min a c ≤ b) (h2 : b ≤ max a c) :
    |b| ≤ max (|a|) (|c|) := by
  rcases le_total a c with h | h
  · rw [min_eq_left h] at h1
    rw [max_eq_right h] at h2
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [neg_abs_le a, le_max_left (|a|) (|c|)]
    · linarith [le_abs_self c, le_max_right (|a|) (|c|)]
  · rw [min_eq_right h] at h1
    rw [max_eq_left h] at h2
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [neg_abs_le c, le_max_right (|a|) (|c|)]
    · linarith [le_abs_self a, le_max_left (|a|) (|c|)]

/-! ## 4. Auxiliary lemmas for the full statement -/

/-- **The fibre function is continuous on any interval free of `B₀`.**  (The `GoodFibre` clause for
that interval.) -/
theorem free_cont {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hgood : GoodFibre Y B₀) {c : Fin k → ℝ} {a b : ℝ} (hab : a < b)
    (hfree : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀) :
    ContinuousOn (fun t => valY Y c t) (Set.Ioo a b) := by
  obtain ⟨hu, -, hcont⟩ := hgood c a b hab hfree
  rw [Metric.continuousOn_iff]
  intro z hz ε hε
  obtain ⟨δ, hδ0, hδ⟩ := hcont z hz ε hε
  refine ⟨δ, hδ0, fun z' hz' hdist => ?_⟩
  have hInDz : Route.InD Y c z := ((hu z hz).exists).imp fun y hy => hy
  have hInDz' : Route.InD Y c z' := ((hu z' hz').exists).imp fun y hy => hy
  have h := hδ z' hz' _ _ (by simpa [Real.dist_eq] using hdist)
    (Route.valY_mem Y c z hInDz) (Route.valY_mem Y c z' hInDz')
  simpa [Real.dist_eq] using h

/-- **The fibre has constant sign on an interval free of `B₀`**: any two of its values there have
positive product. -/
theorem free_sign {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hgood : GoodFibre Y B₀) {c : Fin k → ℝ} {a b : ℝ} (hab : a < b)
    (hfree : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀) {s t : ℝ} (hs : s ∈ Set.Ioo a b)
    (ht : t ∈ Set.Ioo a b) {u v : ℝ} (hu : Gr Y c s u) (hv : Gr Y c t v) : 0 < u * v := by
  obtain ⟨huq, hnz, -⟩ := hgood c a b hab hfree
  have hI : IsPreconnected (Set.Ioo a b) := isPreconnected_Ioo
  have hS : IsPreconnected ((fun t => valY Y c t) '' Set.Ioo a b) :=
    IsPreconnected.image hI (fun t => valY Y c t) (free_cont hgood hab hfree)
  have hOC := hS.ordConnected
  have hus : u = valY Y c s :=
    (huq s hs).unique hu (valY_mem Y c s ((huq s hs).exists.imp fun y hy => hy))
  have hvt : v = valY Y c t :=
    (huq t ht).unique hv (valY_mem Y c t ((huq t ht).exists.imp fun y hy => hy))
  have hmem_s : valY Y c s ∈ (fun t => valY Y c t) '' Set.Ioo a b := ⟨s, hs, rfl⟩
  have hmem_t : valY Y c t ∈ (fun t => valY Y c t) '' Set.Ioo a b := ⟨t, ht, rfl⟩
  have hzero : (0 : ℝ) ∉ (fun t => valY Y c t) '' Set.Ioo a b := by
    rintro ⟨z, hz, hz0⟩
    exact (hnz z hz _ (valY_mem Y c z ((huq z hz).exists.imp fun y hy => hy))) hz0
  rw [hus, hvt]
  have hP : valY Y c s ≠ 0 := hnz s hs _ (valY_mem Y c s ((huq s hs).exists.imp fun y hy => hy))
  have hQ : valY Y c t ≠ 0 := hnz t ht _ (valY_mem Y c t ((huq t ht).exists.imp fun y hy => hy))
  rcases lt_or_gt_of_ne hP with hPs | hPs <;> rcases lt_or_gt_of_ne hQ with hQt | hQt
  · exact mul_pos_of_neg_of_neg hPs hQt
  · exfalso
    exact hzero (hOC.out hmem_s hmem_t ⟨le_of_lt hPs, le_of_lt hQt⟩)
  · exfalso
    exact hzero (hOC.out hmem_t hmem_s ⟨le_of_lt hQt, le_of_lt hPs⟩)
  · exact mul_pos hPs hQt

/-- **The doubling ratio is positive on an interval where both `t` and `2t` are free of `B₀`.** -/
theorem free_ratioY_pos {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hgood : GoodFibre Y B₀) {c : Fin k → ℝ} {a b : ℝ} (hab : a < b)
    (hfree : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀) {t : ℝ} (ht : t ∈ Set.Ioo a b)
    (h2t : 2 * t ∈ Set.Ioo a b) : 0 < ratioY Y c t := by
  obtain ⟨huq, -, -⟩ := hgood c a b hab hfree
  have hInDt : Route.InD Y c t := ((huq t ht).exists).imp fun y hy => hy
  have hInD2t : Route.InD Y c (2 * t) := ((huq (2 * t) h2t).exists).imp fun y hy => hy
  have hpos : 0 < valY Y c t * valY Y c (2 * t) :=
    free_sign hgood hab hfree ht h2t (valY_mem Y c t hInDt) (valY_mem Y c (2 * t) hInD2t)
  rw [ratioY, div_pos_iff]
  rcases mul_pos_iff.mp hpos with h | h
  · exact Or.inl ⟨h.2, h.1⟩
  · exact Or.inr ⟨h.2, h.1⟩

/-- **The doubling ratio is monotone-or-antitone on the part of a free window on which `2t` is
still in the window** (`ULPMStruct`'s ratio claw, transported to the function `ratioY`). -/
theorem ratioY_monoOrAnti {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (hst : ULPMStruct Y B₀) {c : Fin k → ℝ} {u v a b : ℝ} (huv : u < v)
    (hfreeuv : ∀ x ∈ Set.Ioo u v, Fin.cons x c ∉ B₀) (hab : a < b)
    (hsub : Set.Ioo a b ⊆ Set.Ioo u v) (h2 : ∀ x ∈ Set.Ioo a b, 2 * x ∈ Set.Ioo u v) :
    MonotoneOn (ratioY Y c) (Set.Ioo a b) ∨ AntitoneOn (ratioY Y c) (Set.Ioo a b) := by
  refine mono_of_three_point hab ?_
  intro x₁ x₂ x₃ hx₁ hx₂ hx₃ h12 h23
  exact hst.2 c u v huv hfreeuv x₁ x₂ x₃ (ratioY Y c x₁) (ratioY Y c x₂) (ratioY Y c x₃)
    (hsub hx₁) (hsub hx₂) (hsub hx₃) h12 h23
    (ratW_ratioY hfun hst.1 huv hfreeuv (hsub hx₁) (h2 x₁ hx₁))
    (ratW_ratioY hfun hst.1 huv hfreeuv (hsub hx₂) (h2 x₂ hx₂))
    (ratW_ratioY hfun hst.1 huv hfreeuv (hsub hx₃) (h2 x₃ hx₃))

/-- **The fibre is monotone-or-antitone on a closed slot free of the breakpoint family `Bm`**,
whenever the slot lies inside a free window and the three-point trichotomy holds off `Bm`. -/
theorem slot_monoOrAnti {Y : Set (Fin (k + 2) → ℝ)} {B₀ Bm : Set (Fin (k + 1) → ℝ)}
    {c : Fin k → ℝ} {u v t₁ t₂ : ℝ} (huv : u < v)
    (hfreeuv : ∀ x ∈ Set.Ioo u v, Fin.cons x c ∉ B₀)
    (hsub : Set.Icc t₁ t₂ ⊆ Set.Ioo u v) (ht : t₁ < t₂)
    (hB₀free : ∀ x ∈ Set.Ioo t₁ t₂, Fin.cons x c ∉ B₀)
    (hfreeBm : ∀ x ∈ Set.Ioo t₁ t₂, Fin.cons x c ∉ Bm)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (hgf : GoodFibre Y B₀)
    (htri : ∀ c : Fin k → ℝ, ∀ a b : ℝ, a < b → (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ Bm) →
      ∀ x₁ x₂ x₃ y₁ y₂ y₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b → x₃ ∈ Set.Ioo a b →
        x₁ < x₂ → x₂ < x₃ → Gr Y c x₁ y₁ → Gr Y c x₂ y₂ → Gr Y c x₃ y₃ →
        (y₁ ≤ y₂ ∧ y₂ ≤ y₃) ∨ (y₃ ≤ y₂ ∧ y₂ ≤ y₁)) :
    MonotoneOn (valY Y c) (Set.Icc t₁ t₂) ∨ AntitoneOn (valY Y c) (Set.Icc t₁ t₂) := by
  have hmono := mono_valY_of_trichotomy (Y := Y) (B := B₀) (c := c) (a := t₁) (b := t₂)
    hfun hgf ht hB₀free (htri c t₁ t₂ ht hfreeBm)
  exact monoOn_Icc_of_Ioo ht hmono ((free_cont hgf huv hfreeuv).mono hsub)

/-- On a slot `[t, 2t]` on which the fibre is monotone-or-antitone and where the doubling ratio at
`t` is at most `Λ ≥ 1`, every fibre value on the slot is bounded by `Λ` times the value at `t`. -/
theorem abs_le_of_slot_mono {F : ℝ → ℝ} {t Λ : ℝ} (ht : 0 < t) (hΛ : 1 ≤ Λ)
    (hmono : MonotoneOn F (Set.Icc t (2 * t)) ∨ AntitoneOn F (Set.Icc t (2 * t)))
    (hrat : |F (2 * t)| ≤ Λ * |F t|) {s : ℝ} (hs : s ∈ Set.Icc t (2 * t)) :
    |F s| ≤ Λ * |F t| := by
  have ht2 : t ≤ 2 * t := by linarith
  have h1 : |F s| ≤ max (|F t|) (|F (2 * t)|) := by
    have hts : t ∈ Set.Icc t (2 * t) := ⟨le_rfl, ht2⟩
    have h2tI : 2 * t ∈ Set.Icc t (2 * t) := ⟨ht2, le_rfl⟩
    refine abs_le_max_abs_of_between ?_ ?_
    · rcases hmono with hm | ha
      · exact le_trans (min_le_left (F t) (F (2 * t))) (hm hts hs hs.1)
      · exact le_trans (min_le_right (F t) (F (2 * t))) (ha hs h2tI hs.2)
    · rcases hmono with hm | ha
      · exact le_trans (hm hs h2tI hs.2) (le_max_right (F t) (F (2 * t)))
      · exact le_trans (ha hts hs hs.1) (le_max_left (F t) (F (2 * t)))
  have h2 : max (|F t|) (|F (2 * t)|) ≤ Λ * |F t| := by
    refine max_le ?_ hrat
    nlinarith [abs_nonneg (F t)]
  linarith

/-- Product comparison with a nonnegative left factor (local form, avoiding `MulLeftMono`). -/
theorem prod_le_prod_of_le {f g : ℕ → ℝ} {s : Finset ℕ} (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have ha0 : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
    have ha1 : f a ≤ g a := h1 a (Finset.mem_insert_self a s)
    have hs0 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
    have hs1 : (∏ i ∈ s, f i) ≤ (∏ i ∈ s, g i) :=
      ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    exact mul_le_mul ha1 hs1 hs0 (le_trans ha0 ha1)

/-- Telescoping identity for the doubling chain: `G (2^J x) = (∏_{j<J} ρ (2^j x)) · G x`. -/
theorem telescoping_up {G ρ : ℝ → ℝ} (x : ℝ) (J : ℕ)
    (h : ∀ j < J, G (2 * ((2 : ℝ) ^ j * x)) = ρ ((2 : ℝ) ^ j * x) * G ((2 : ℝ) ^ j * x)) :
    G ((2 : ℝ) ^ J * x) = (∏ j ∈ Finset.range J, ρ ((2 : ℝ) ^ j * x)) * G x := by
  induction J with
  | zero => simp
  | succ n ih =>
    have h' : ∀ j < n, G (2 * ((2 : ℝ) ^ j * x)) = ρ ((2 : ℝ) ^ j * x) * G ((2 : ℝ) ^ j * x) :=
      fun j hj => h j (Nat.lt_succ_of_lt hj)
    have hstep : G (2 * ((2 : ℝ) ^ n * x)) = ρ ((2 : ℝ) ^ n * x) * G ((2 : ℝ) ^ n * x) :=
      h n (Nat.lt_succ_self n)
    have hpow : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by rw [pow_succ]; ring
    have ih' := ih h'
    rw [Finset.prod_range_succ, hpow, mul_assoc, hstep, ih']
    ring

/-- Telescoping identity for the halving chain: `G x = (∏_{j<J} ρ (x / 2^{j+1})) · G (x / 2^J)`. -/
theorem telescoping_down {G ρ : ℝ → ℝ} (x : ℝ) (J : ℕ)
    (h : ∀ j < J, G (2 * (x / (2 : ℝ) ^ (j + 1))) =
      ρ (x / (2 : ℝ) ^ (j + 1)) * G (x / (2 : ℝ) ^ (j + 1))) :
    G x = (∏ j ∈ Finset.range J, ρ (x / (2 : ℝ) ^ (j + 1))) * G (x / (2 : ℝ) ^ J) := by
  induction J with
  | zero => simp
  | succ n ih =>
    have h' : ∀ j < n, G (2 * (x / (2 : ℝ) ^ (j + 1))) =
        ρ (x / (2 : ℝ) ^ (j + 1)) * G (x / (2 : ℝ) ^ (j + 1)) :=
      fun j hj => h j (Nat.lt_succ_of_lt hj)
    rw [ih h', Finset.prod_range_succ]
    have hstep : G (2 * (x / (2 : ℝ) ^ (n + 1))) =
        ρ (x / (2 : ℝ) ^ (n + 1)) * G (x / (2 : ℝ) ^ (n + 1)) :=
      h n (Nat.lt_succ_self n)
    have hx : 2 * (x / (2 : ℝ) ^ (n + 1)) = x / (2 : ℝ) ^ n := by
      rw [pow_succ]
      field_simp
    rw [← hx, hstep]
    ring

/-- **Case A chain.**  If `G (2x) = ρ x · G x` along the doubling chain and `ρ` is nondecreasing
there, then the rise over the pair `(z, z')` is at most the rise over `(2^J z, 2^J z')`. -/
theorem rise_le_shift_up {G ρ : ℝ → ℝ} {z z' : ℝ} {J : ℕ}
    (hprod : G ((2 : ℝ) ^ J * z) = (∏ j ∈ Finset.range J, ρ ((2 : ℝ) ^ j * z)) * G z)
    (hprod' : G ((2 : ℝ) ^ J * z') = (∏ j ∈ Finset.range J, ρ ((2 : ℝ) ^ j * z')) * G z')
    (hpos : 0 < G z) (hpos' : 0 < G z')
    (hmono : ∀ j < J, ρ ((2 : ℝ) ^ j * z) ≤ ρ ((2 : ℝ) ^ j * z'))
    (hρnn : ∀ j < J, 0 ≤ ρ ((2 : ℝ) ^ j * z)) :
    G z' * G ((2 : ℝ) ^ J * z) ≤ G ((2 : ℝ) ^ J * z') * G z := by
  rw [hprod, hprod']
  have hle : (∏ j ∈ Finset.range J, ρ ((2 : ℝ) ^ j * z)) ≤
      (∏ j ∈ Finset.range J, ρ ((2 : ℝ) ^ j * z')) :=
    prod_le_prod_of_le (fun j hj => hρnn j (Finset.mem_range.mp hj))
      (fun j hj => hmono j (Finset.mem_range.mp hj))
  calc G z' * ((∏ j ∈ Finset.range J, ρ ((2 : ℝ) ^ j * z)) * G z)
      = (∏ j ∈ Finset.range J, ρ ((2 : ℝ) ^ j * z)) * (G z * G z') := by ring
    _ ≤ (∏ j ∈ Finset.range J, ρ ((2 : ℝ) ^ j * z')) * (G z * G z') :=
        mul_le_mul_of_nonneg_right hle (le_of_lt (mul_pos hpos hpos'))
    _ = ((∏ j ∈ Finset.range J, ρ ((2 : ℝ) ^ j * z')) * G z') * G z := by ring

/-- **Case B chain.**  If `G (2x) = ρ x · G x` along the halving chain and `ρ` is nonincreasing
there, then the rise over `(z, z')` is at most the rise over `(z/2^J, z'/2^J)`. -/
theorem rise_le_shift_down {G ρ : ℝ → ℝ} {z z' : ℝ} {J : ℕ}
    (hprod : G z = (∏ j ∈ Finset.range J, ρ (z / (2 : ℝ) ^ (j + 1))) * G (z / (2 : ℝ) ^ J))
    (hprod' : G z' = (∏ j ∈ Finset.range J, ρ (z' / (2 : ℝ) ^ (j + 1))) * G (z' / (2 : ℝ) ^ J))
    (hA : 0 ≤ G (z / (2 : ℝ) ^ J)) (hB : 0 ≤ G (z' / (2 : ℝ) ^ J))
    (hmono : ∀ j < J, ρ (z' / (2 : ℝ) ^ (j + 1)) ≤ ρ (z / (2 : ℝ) ^ (j + 1)))
    (hρnn : ∀ j < J, 0 ≤ ρ (z' / (2 : ℝ) ^ (j + 1))) :
    G z' * G (z / (2 : ℝ) ^ J) ≤ G (z' / (2 : ℝ) ^ J) * G z := by
  rw [hprod, hprod']
  have hle : (∏ j ∈ Finset.range J, ρ (z' / (2 : ℝ) ^ (j + 1))) ≤
      (∏ j ∈ Finset.range J, ρ (z / (2 : ℝ) ^ (j + 1))) :=
    prod_le_prod_of_le (fun j hj => hρnn j (Finset.mem_range.mp hj))
      (fun j hj => hmono j (Finset.mem_range.mp hj))
  have key := mul_le_mul_of_nonneg_right hle (mul_nonneg hB hA)
  calc (∏ j ∈ Finset.range J, ρ (z' / (2 : ℝ) ^ (j + 1))) * G (z' / (2 : ℝ) ^ J) *
        G (z / (2 : ℝ) ^ J)
      = (∏ j ∈ Finset.range J, ρ (z' / (2 : ℝ) ^ (j + 1))) *
          (G (z' / (2 : ℝ) ^ J) * G (z / (2 : ℝ) ^ J)) := by ring
    _ ≤ (∏ j ∈ Finset.range J, ρ (z / (2 : ℝ) ^ (j + 1))) *
          (G (z' / (2 : ℝ) ^ J) * G (z / (2 : ℝ) ^ J)) := key
    _ = G (z' / (2 : ℝ) ^ J) *
          ((∏ j ∈ Finset.range J, ρ (z / (2 : ℝ) ^ (j + 1))) * G (z / (2 : ℝ) ^ J)) := by ring

/-- **Pigeonhole for slots.**  If `P` has at most `K` elements and the `K+1` slots
`(lo i, hi i)`, `i ≤ K`, are pairwise disjoint, then one of them is disjoint from `P`. -/
theorem exists_free_slot {P : Set ℝ} {K : ℕ} (hP : P.encard ≤ K) (lo hi : ℕ → ℝ)
    (hdis : ∀ i j : ℕ, i < j → Disjoint (Set.Ioo (lo i) (hi i)) (Set.Ioo (lo j) (hi j))) :
    ∃ i : ℕ, i ≤ K ∧ ∀ p ∈ P, ¬ (lo i < p ∧ p < hi i) := by
  by_contra hcon
  push_neg at hcon
  have hchoice : ∀ i : Fin (K + 1), ∃ p : ℝ, p ∈ P ∧ lo (i : ℕ) < p ∧ p < hi (i : ℕ) :=
    fun i => hcon (i : ℕ) (Nat.lt_succ_iff.mp i.isLt)
  choose f hfP hflo hfhi using hchoice
  obtain ⟨i, j, hij, heq⟩ := (encardLePigeonhole P K).mp hP f (fun i => hfP i)
  have hd := hdis (i : ℕ) (j : ℕ) hij
  rw [Set.disjoint_left] at hd
  exact (hd ⟨hflo i, hfhi i⟩) (by rw [heq]; exact ⟨hflo j, hfhi j⟩)


end Work.WilC4
