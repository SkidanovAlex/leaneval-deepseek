import Mathlib
import Submission.Lib.Unif2.Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract
import Submission.Lib.Unif2.Commons.Topology.Plane.exists_fold_unitSq
import Submission.Lib.Unif2.Commons.Topology.Plane.exists_cwComplex_of_finset_segments

open Set

noncomputable section

namespace Commons.Topology.Plane

/-! ## Definitions -/

def uSq : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1}
def uInt : Set ℂ := {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < 1}
def uOpenTop : Set ℂ := {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ z.im = 1}
def uSqU : Set ℂ :=
  {z : ℂ | (z.re = 0 ∧ 0 ≤ z.im ∧ z.im ≤ 1) ∨ (z.re = 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1) ∨
           (z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1)}
def uCore : Set ℂ := uSq \ (uInt ∪ uOpenTop)

def dSq (n : ℕ) (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | (p.1 : ℝ) / 2 ^ n ≤ z.re ∧ z.re ≤ ((p.1 : ℝ) + 1) / 2 ^ n ∧
           (p.2 : ℝ) / 2 ^ n ≤ z.im ∧ z.im ≤ ((p.2 : ℝ) + 1) / 2 ^ n}

def dInt (n : ℕ) (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | (p.1 : ℝ) / 2 ^ n < z.re ∧ z.re < ((p.1 : ℝ) + 1) / 2 ^ n ∧
           (p.2 : ℝ) / 2 ^ n < z.im ∧ z.im < ((p.2 : ℝ) + 1) / 2 ^ n}

def dOpenTop (n : ℕ) (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | (p.1 : ℝ) / 2 ^ n < z.re ∧ z.re < ((p.1 : ℝ) + 1) / 2 ^ n ∧
           z.im = ((p.2 : ℝ) + 1) / 2 ^ n}

def dCore (n : ℕ) (p : ℤ × ℤ) : Set ℂ := dSq n p \ (dInt n p ∪ dOpenTop n p)

def dAff (a c δ : ℝ) (z : ℂ) : ℂ := ⟨a + δ * z.re, c + δ * z.im⟩
def dInv (a c δ : ℝ) (w : ℂ) : ℂ := ⟨(w.re - a) / δ, (w.im - c) / δ⟩

lemma dAff_re (a c δ : ℝ) (z : ℂ) : (dAff a c δ z).re = a + δ * z.re := rfl
lemma dAff_im (a c δ : ℝ) (z : ℂ) : (dAff a c δ z).im = c + δ * z.im := rfl
lemma dInv_re (a c δ : ℝ) (z : ℂ) : (dInv a c δ z).re = (z.re - a) / δ := rfl
lemma dInv_im (a c δ : ℝ) (z : ℂ) : (dInv a c δ z).im = (z.im - c) / δ := rfl

lemma dInv_dAff {a c δ : ℝ} (hδ : δ ≠ 0) (z : ℂ) : dInv a c δ (dAff a c δ z) = z := by
  apply Complex.ext
  · rw [dInv_re, dAff_re]; field_simp; ring
  · rw [dInv_im, dAff_im]; field_simp; ring

lemma dAff_dInv {a c δ : ℝ} (hδ : δ ≠ 0) (z : ℂ) : dAff a c δ (dInv a c δ z) = z := by
  apply Complex.ext
  · rw [dAff_re, dInv_re]; field_simp; ring
  · rw [dAff_im, dInv_im]; field_simp; ring

lemma dAff_injective {a c δ : ℝ} (hδ : δ ≠ 0) : Function.Injective (dAff a c δ) := by
  intro z w h
  have h1 : δ * z.re = δ * w.re := by
    have := congrArg Complex.re h; rw [dAff_re, dAff_re] at this; linarith
  have h2 : δ * z.im = δ * w.im := by
    have := congrArg Complex.im h; rw [dAff_im, dAff_im] at this; linarith
  exact Complex.ext (mul_left_cancel₀ hδ h1) (mul_left_cancel₀ hδ h2)

lemma image_sdiff_of_injective {f : ℂ → ℂ} (hf : Function.Injective f) (s t : Set ℂ) :
    f '' (s \ t) = f '' s \ f '' t := by
  ext w; constructor
  · rintro ⟨z, ⟨hz, hzt⟩, rfl⟩
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro ⟨z', hz', he⟩
    exact hzt (by rw [← hf he]; exact hz')
  · rintro ⟨⟨z, hz, rfl⟩, hnot⟩
    exact ⟨z, ⟨hz, fun hzt => hnot ⟨z, hzt, rfl⟩⟩, rfl⟩

lemma uCore_eq_uSqU : uCore = uSqU := by
  ext z
  simp only [uCore, uSq, uInt, uOpenTop, uSqU, Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨h1,h2,h3,h4⟩, hnot⟩
    rw [not_or] at hnot
    obtain ⟨h5, h6⟩ := hnot
    rcases eq_or_lt_of_le h1 with hre0 | hrepos
    · exact Or.inl ⟨hre0.symm, h3, h4⟩
    rcases lt_or_eq_of_le h2 with hre1 | hre1
    · rcases eq_or_lt_of_le h3 with him0 | himpos
      · exact Or.inr (Or.inr ⟨him0.symm, h1, h2⟩)
      rcases lt_or_eq_of_le h4 with him1 | him1
      · exact absurd ⟨hrepos, hre1, himpos, him1⟩ h5
      · exact absurd ⟨hrepos, hre1, him1⟩ h6
    · exact Or.inr (Or.inl ⟨hre1, h3, h4⟩)
  · rintro (⟨h1,h3,h4⟩ | ⟨h1,h3,h4⟩ | ⟨h1,h3,h4⟩)
    · refine ⟨⟨by linarith, by linarith, h3, h4⟩, ?_⟩
      rw [not_or]
      exact ⟨fun h => absurd h.1 (by linarith), fun h => absurd h.1 (by linarith)⟩
    · refine ⟨⟨by linarith, by linarith, h3, h4⟩, ?_⟩
      rw [not_or]
      exact ⟨fun h => absurd h.2.1 (by linarith), fun h => absurd h.2.1 (by linarith)⟩
    · refine ⟨⟨h3, h4, by linarith, by linarith⟩, ?_⟩
      rw [not_or]
      exact ⟨fun h => absurd h.2.2 (by linarith), fun h => absurd h.2.2 (by linarith)⟩

/-! ## The similarity -/

lemma dSq_eq_image (n : ℕ) (p : ℤ × ℤ) :
    dSq n p = dAff ((p.1 : ℝ) / 2 ^ n) ((p.2 : ℝ) / 2 ^ n) (1 / 2 ^ n) '' uSq := by
  have hδ0 : (0:ℝ) < 1 / 2 ^ n := by positivity
  have hδne : (1/2^n : ℝ) ≠ 0 := ne_of_gt hδ0
  have hb : (p.1 : ℝ) / 2 ^ n + 1 / 2 ^ n = ((p.1 : ℝ) + 1) / 2 ^ n := by ring
  have hd : (p.2 : ℝ) / 2 ^ n + 1 / 2 ^ n = ((p.2 : ℝ) + 1) / 2 ^ n := by ring
  ext w
  simp only [dSq, uSq, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hw
    refine ⟨dInv ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n) w, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [dInv_re]; exact div_nonneg (by linarith [hw.1]) (le_of_lt hδ0)
    · rw [dInv_re, div_le_iff₀ hδ0]; linarith [hw.2.1]
    · rw [dInv_im]; exact div_nonneg (by linarith [hw.2.2.1]) (le_of_lt hδ0)
    · rw [dInv_im, div_le_iff₀ hδ0]; linarith [hw.2.2.2]
    · exact dAff_dInv hδne w
  · rintro ⟨u, ⟨hu1,hu2,hu3,hu4⟩, rfl⟩
    rw [dAff_re, dAff_im]
    have h0 : (0:ℝ) ≤ 1/2^n := le_of_lt hδ0
    refine ⟨?_, ?_, ?_, ?_⟩
    · nlinarith [mul_nonneg hu1 h0]
    · rw [← hb]; nlinarith [mul_le_of_le_one_right h0 hu2]
    · nlinarith [mul_nonneg hu3 h0]
    · rw [← hd]; nlinarith [mul_le_of_le_one_right h0 hu4]

lemma dInt_eq_image (n : ℕ) (p : ℤ × ℤ) :
    dInt n p = dAff ((p.1 : ℝ) / 2 ^ n) ((p.2 : ℝ) / 2 ^ n) (1 / 2 ^ n) '' uInt := by
  have hδ0 : (0:ℝ) < 1 / 2 ^ n := by positivity
  have hδne : (1/2^n : ℝ) ≠ 0 := ne_of_gt hδ0
  have hb : (p.1 : ℝ) / 2 ^ n + 1 / 2 ^ n = ((p.1 : ℝ) + 1) / 2 ^ n := by ring
  have hd : (p.2 : ℝ) / 2 ^ n + 1 / 2 ^ n = ((p.2 : ℝ) + 1) / 2 ^ n := by ring
  ext w
  simp only [dInt, uInt, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hw
    obtain ⟨hw1,hw2,hw3,hw4⟩ := hw
    refine ⟨dInv ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n) w, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [dInv_re, lt_div_iff₀ hδ0]; linarith
    · rw [dInv_re, div_lt_iff₀ hδ0]; linarith
    · rw [dInv_im, lt_div_iff₀ hδ0]; linarith
    · rw [dInv_im, div_lt_iff₀ hδ0]; linarith
    · exact dAff_dInv hδne w
  · rintro ⟨u, ⟨hu1,hu2,hu3,hu4⟩, rfl⟩
    rw [dAff_re, dAff_im]
    have h0 : (0:ℝ) < 1/2^n := hδ0
    refine ⟨?_, ?_, ?_, ?_⟩
    · nlinarith [mul_pos hu1 h0]
    · rw [← hb]; nlinarith [mul_lt_of_lt_one_right h0 hu2]
    · nlinarith [mul_pos hu3 h0]
    · rw [← hd]; nlinarith [mul_lt_of_lt_one_right h0 hu4]

lemma dOpenTop_eq_image (n : ℕ) (p : ℤ × ℤ) :
    dOpenTop n p = dAff ((p.1 : ℝ) / 2 ^ n) ((p.2 : ℝ) / 2 ^ n) (1 / 2 ^ n) '' uOpenTop := by
  have hδ0 : (0:ℝ) < 1 / 2 ^ n := by positivity
  have hδne : (1/2^n : ℝ) ≠ 0 := ne_of_gt hδ0
  have hb : (p.1 : ℝ) / 2 ^ n + 1 / 2 ^ n = ((p.1 : ℝ) + 1) / 2 ^ n := by ring
  have hd : (p.2 : ℝ) / 2 ^ n + 1 / 2 ^ n = ((p.2 : ℝ) + 1) / 2 ^ n := by ring
  ext w
  simp only [dOpenTop, uOpenTop, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hw
    obtain ⟨hw1,hw2,hw3⟩ := hw
    refine ⟨dInv ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n) w, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [dInv_re, lt_div_iff₀ hδ0]; linarith
    · rw [dInv_re, div_lt_iff₀ hδ0]; linarith
    · rw [dInv_im, hw3]
      rw [show (((p.2:ℝ)+1)/2^n - (p.2:ℝ)/2^n) = 1/2^n by ring, div_self hδne]
    · exact dAff_dInv hδne w
  · rintro ⟨u, ⟨hu1,hu2,hu3⟩, rfl⟩
    rw [dAff_re, dAff_im]
    have h0 : (0:ℝ) < 1/2^n := hδ0
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [mul_pos hu1 h0]
    · rw [← hb]; nlinarith [mul_lt_of_lt_one_right h0 hu2]
    · rw [← hd]; nlinarith [hu3]

lemma dCore_eq_image (n : ℕ) (p : ℤ × ℤ) :
    dCore n p = dAff ((p.1 : ℝ) / 2 ^ n) ((p.2 : ℝ) / 2 ^ n) (1 / 2 ^ n) '' uCore := by
  have hδne : (1/2^n : ℝ) ≠ 0 := by positivity
  rw [dCore, uCore, dSq_eq_image, dInt_eq_image, dOpenTop_eq_image,
    image_sdiff_of_injective (dAff_injective hδne), image_union]


lemma continuous_dAff (a c δ : ℝ) : Continuous (dAff a c δ) := by
  have h : (dAff a c δ) = fun z : ℂ =>
      ((a : ℂ) + (δ : ℂ) * ((z.re : ℂ))) + (((c : ℂ) + (δ : ℂ) * ((z.im : ℂ))) * Complex.I) := by
    funext z; apply Complex.ext <;> simp [dAff]
  rw [h]; fun_prop

lemma continuous_dInv (a c δ : ℝ) : Continuous (dInv a c δ) := by
  have h : (dInv a c δ) = fun z : ℂ =>
      (((z.re - a) / δ : ℝ) : ℂ) + ((((z.im - c) / δ : ℝ) : ℂ)) * Complex.I := by
    funext z; apply Complex.ext <;> simp [dInv]
  rw [h]; fun_prop

lemma dInv_mem_uSq {n : ℕ} {p : ℤ × ℤ} {z : ℂ} (hz : z ∈ dSq n p) :
    dInv ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n) z ∈ uSq := by
  have hδne : (1/2^n : ℝ) ≠ 0 := by positivity
  rw [dSq_eq_image] at hz
  obtain ⟨u, hu, heq⟩ := hz
  have h1 : dAff ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n)
        (dInv ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n) z) =
      dAff ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n) u := by
    rw [dAff_dInv hδne, heq]
  rw [dAff_injective hδne h1]; exact hu

structure DFold (n : ℕ) (p : ℤ × ℤ) where
  φ : ℂ → ℂ
  H : ℂ × unitInterval → ℂ
  contφ : ContinuousOn φ (dSq n p)
  contH : ContinuousOn H (dSq n p ×ˢ Set.univ)
  Hmem : ∀ z ∈ dSq n p, ∀ t : unitInterval, H (z, t) ∈ dSq n p
  Hzero : ∀ z ∈ dSq n p, H (z, (0:unitInterval)) = z
  Hone : ∀ z ∈ dSq n p, H (z, (1:unitInterval)) = φ z
  φmem : ∀ z ∈ dSq n p, φ z ∈ dCore n p
  φfix : ∀ z ∈ dCore n p, φ z = z
  φout : ∀ z, z ∉ dSq n p → φ z = z
  Hfix : ∀ z ∈ dCore n p, ∀ t : unitInterval, H (z, t) = z
  Hout : ∀ z, z ∉ dSq n p → ∀ t : unitInterval, H (z, t) = z

def DFold.ofUnit (n : ℕ) (p : ℤ × ℤ) (uφ : ℂ → ℂ) (uH : ℂ × unitInterval → ℂ)
    (hcontφ : ContinuousOn uφ uSq) (hcontH : ContinuousOn uH (uSq ×ˢ Set.univ))
    (hHmem : ∀ z ∈ uSq, ∀ t : unitInterval, uH (z, t) ∈ uSq)
    (hH0 : ∀ z ∈ uSq, uH (z, (0:unitInterval)) = z)
    (hH1 : ∀ z ∈ uSq, uH (z, (1:unitInterval)) = uφ z)
    (hφmem : ∀ z ∈ uSq, uφ z ∈ uSqU) (hφfix : ∀ z ∈ uSqU, uφ z = z)
    (hφout : ∀ z, z ∉ uSq → uφ z = z)
    (hHfix : ∀ z ∈ uSqU, ∀ t : unitInterval, uH (z, t) = z)
    (hHout : ∀ z, z ∉ uSq → ∀ t : unitInterval, uH (z, t) = z) : DFold n p := by
  have hδne : (1/2^n : ℝ) ≠ 0 := by positivity
  have hcontInv : Continuous (dInv ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n)) :=
    continuous_dInv _ _ _
  have hcontAff : Continuous (dAff ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n)) :=
    continuous_dAff _ _ _
  have hmaps : MapsTo (dInv ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n)) (dSq n p) uSq :=
    fun z hz => dInv_mem_uSq hz
  have hcompφ : ContinuousOn
      (fun w => uφ (dInv ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n) w)) (dSq n p) :=
    hcontφ.comp hcontInv.continuousOn hmaps
  have hmaps2 : MapsTo (fun q : ℂ × unitInterval =>
        (dInv ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n) q.1, q.2))
      (dSq n p ×ˢ Set.univ) (uSq ×ˢ Set.univ) := by
    rintro ⟨z,t⟩ ⟨hz, -⟩; exact ⟨hmaps hz, Set.mem_univ _⟩
  have hpair : Continuous (fun q : ℂ × unitInterval =>
      (dInv ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n) q.1, q.2)) :=
    continuous_prodMk.mpr ⟨hcontInv.comp continuous_fst, continuous_snd⟩
  have hcompH : ContinuousOn (fun q : ℂ × unitInterval =>
      uH (dInv ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n) q.1, q.2)) (dSq n p ×ˢ Set.univ) :=
    hcontH.comp hpair.continuousOn hmaps2
  exact
    { φ := fun w => dAff ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n)
        (uφ (dInv ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n) w))
      H := fun q => dAff ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n)
        (uH (dInv ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n) q.1, q.2))
      contφ := hcontAff.continuousOn.comp hcompφ (fun z _ => Set.mem_univ _)
      contH := hcontAff.continuousOn.comp hcompH (fun z _ => Set.mem_univ _)
      Hmem := fun z hz t => by
        rw [dSq_eq_image]
        exact ⟨_, hHmem _ (dInv_mem_uSq hz) t, rfl⟩
      Hzero := fun z hz => by
        rw [hH0 _ (dInv_mem_uSq hz), dAff_dInv hδne z]
      Hone := fun z hz => by
        rw [hH1 _ (dInv_mem_uSq hz)]
      φmem := fun z hz => by
        rw [dCore_eq_image]
        exact ⟨_, (uCore_eq_uSqU ▸ hφmem _ (dInv_mem_uSq hz)), rfl⟩
      φfix := fun z hz => by
        rw [dCore_eq_image] at hz
        obtain ⟨u, hu, rfl⟩ := hz
        rw [dInv_dAff hδne, hφfix u (uCore_eq_uSqU ▸ hu)]
      φout := fun z hz => by
        have hz' : dInv ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n) z ∉ uSq := by
          intro h
          exact hz (by rw [dSq_eq_image]; exact ⟨_, h, (dAff_dInv hδne z)⟩)
        rw [hφout _ hz', dAff_dInv hδne z]
      Hfix := fun z hz t => by
        rw [dCore_eq_image] at hz
        obtain ⟨u, hu, rfl⟩ := hz
        rw [dInv_dAff hδne, hHfix u (uCore_eq_uSqU ▸ hu) t]
      Hout := fun z hz t => by
        have hz' : dInv ((p.1:ℝ)/2^n) ((p.2:ℝ)/2^n) (1/2^n) z ∉ uSq := by
          intro h
          exact hz (by rw [dSq_eq_image]; exact ⟨_, h, (dAff_dInv hδne z)⟩)
        rw [hHout _ hz' t, dAff_dInv hδne z] }


/-! ## The removed set, the tall rectangle, and the current space -/

def dRemoved (n : ℕ) (p : ℤ × ℤ) : Set ℂ := dInt n p ∪ dOpenTop n p

def dN (n : ℕ) (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | (p.1 : ℝ) / 2 ^ n < z.re ∧ z.re < ((p.1 : ℝ) + 1) / 2 ^ n ∧
           (p.2 : ℝ) / 2 ^ n < z.im ∧ z.im < ((p.2 : ℝ) + 2) / 2 ^ n}

def YSet (n : ℕ) (S A : Finset (ℤ × ℤ)) : Set ℂ :=
  (⋃ p ∈ S, dSq n p) \ (⋃ p ∈ A, dRemoved n p)

lemma dInt_subset_dSq (n : ℕ) (p : ℤ × ℤ) : dInt n p ⊆ dSq n p := by
  intro z hz; obtain ⟨h1,h2,h3,h4⟩ := hz; exact ⟨le_of_lt h1, le_of_lt h2, le_of_lt h3, le_of_lt h4⟩

lemma dInt_subset_dN (n : ℕ) (p : ℤ × ℤ) : dInt n p ⊆ dN n p := by
  intro z hz; obtain ⟨h1,h2,h3,h4⟩ := hz
  refine ⟨h1, h2, h3, ?_⟩
  have : (p.2 : ℝ) + 1 < (p.2 : ℝ) + 2 := by norm_num
  linarith [show z.im < ((p.2:ℝ)+1)/2^n from h4, div_lt_div_of_pos_right this (by positivity : (0:ℝ) < 2^n)]

lemma dOpenTop_subset_dN (n : ℕ) (p : ℤ × ℤ) : dOpenTop n p ⊆ dN n p := by
  intro z hz; obtain ⟨h1,h2,h3⟩ := hz
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [h3]; exact div_lt_div_of_pos_right (by norm_num) (by positivity : (0:ℝ) < 2^n)
  · rw [h3]; exact div_lt_div_of_pos_right (by norm_num) (by positivity : (0:ℝ) < 2^n)

lemma isOpen_dN (n : ℕ) (p : ℤ × ℤ) : IsOpen (dN n p) := by
  have h : dN n p = (fun z : ℂ => (z.re, z.im)) ⁻¹'
      (Set.Ioo ((p.1:ℝ)/2^n) (((p.1:ℝ)+1)/2^n) ×ˢ
       Set.Ioo ((p.2:ℝ)/2^n) (((p.2:ℝ)+2)/2^n)) := by
    ext z; simp only [dN, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Ioo]; tauto
  rw [h]
  exact (isOpen_Ioo.prod isOpen_Ioo).preimage (by fun_prop)

/-! ## A point of a grid square lying in the tall rectangle -/

lemma grid_index_of_mem {n : ℕ} {p q : ℤ × ℤ} {z : ℂ}
    (hq : z ∈ dSq n q) (hN : z ∈ dN n p) :
    q.1 = p.1 ∧ (q.2 = p.2 ∨ q.2 = p.2 + 1) := by
  obtain ⟨hq1,hq2,hq3,hq4⟩ := hq
  obtain ⟨hN1,hN2,hN3,hN4⟩ := hN
  have h2n : (0:ℝ) < 2^n := by positivity
  have hz1 : q.1 = p.1 := by
    have hA : q.1 ≤ p.1 := by
      have e1 : (↑q.1) ≤ z.re * 2^n := (div_le_iff₀ h2n).mp hq1
      have e2 : z.re * 2^n < (↑p.1 + 1) := (lt_div_iff₀ h2n).mp hN2
      have : (q.1:ℝ) < (p.1:ℝ) + 1 := by linarith
      have : q.1 < p.1 + 1 := by exact_mod_cast this
      omega
    have hB : p.1 ≤ q.1 := by
      have e1 : (↑p.1) < z.re * 2^n := (div_lt_iff₀ h2n).mp hN1
      have e2 : z.re * 2^n ≤ (↑q.1 + 1) := (le_div_iff₀ h2n).mp hq2
      have : (p.1:ℝ) < (q.1:ℝ) + 1 := by linarith
      have : p.1 < q.1 + 1 := by exact_mod_cast this
      omega
    omega
  refine ⟨hz1, ?_⟩
  have hA : q.2 ≤ p.2 + 1 := by
    have e1 : (↑q.2) ≤ z.im * 2^n := (div_le_iff₀ h2n).mp hq3
    have e2 : z.im * 2^n < (↑p.2 + 2) := (lt_div_iff₀ h2n).mp hN4
    have : (q.2:ℝ) < (p.2:ℝ) + 2 := by linarith
    have : q.2 < p.2 + 2 := by exact_mod_cast this
    omega
  have hB : p.2 ≤ q.2 := by
    have e1 : (↑p.2) < z.im * 2^n := (div_lt_iff₀ h2n).mp hN3
    have e2 : z.im * 2^n ≤ (↑q.2 + 1) := (le_div_iff₀ h2n).mp hq4
    have : (p.2:ℝ) < (q.2:ℝ) + 1 := by linarith
    have : p.2 < q.2 + 1 := by exact_mod_cast this
    omega
  omega

lemma mem_dSq_of_mem_YSet_dN {n : ℕ} {S A : Finset (ℤ × ℤ)} {p : ℤ × ℤ} {z : ℂ}
    (hup : (p.1, p.2+1) ∈ S → (p.1, p.2+1) ∈ A)
    (hz : z ∈ YSet n S A) (hzN : z ∈ dN n p) : z ∈ dSq n p := by
  obtain ⟨hzN1,hzN2,hzN3,hzN4⟩ := hzN
  obtain ⟨hzK, hznot⟩ := hz
  obtain ⟨q, hqS, hzq⟩ := Set.mem_iUnion₂.mp hzK
  obtain ⟨hq1, hq2 | hq2⟩ := grid_index_of_mem hzq ⟨hzN1,hzN2,hzN3,hzN4⟩
  · rw [Prod.ext hq1 hq2] at hzq; exact hzq
  · have hq' : q = (p.1, p.2 + 1) := Prod.ext hq1 hq2
    by_cases him : z.im ≤ ((p.2:ℝ)+1)/2^n
    · exact ⟨le_of_lt hzN1, le_of_lt hzN2, le_of_lt hzN3, him⟩
    · exfalso
      have hpgrid : (p.1, p.2+1) ∈ S := hq' ▸ hqS
      have hpA := hup hpgrid
      have hzup : z ∈ dRemoved n (p.1, p.2+1) := by
        left
        refine ⟨hzN1, hzN2, ?_, ?_⟩
        · have hcast : (((p.2+1:ℤ)):ℝ) = (p.2:ℝ) + 1 := by push_cast; ring
          rw [hcast]; exact lt_of_not_ge him
        · have hcast : (((p.2+1:ℤ)):ℝ) + 1 = (p.2:ℝ) + 2 := by push_cast; ring
          rw [hcast]; exact hzN4
      exact hznot (Set.mem_iUnion₂.mpr ⟨_, hpA, hzup⟩)


/-! ## Index comparisons -/

lemma int_le_of_div_lt_le {n : ℕ} {a b : ℤ} {x : ℝ}
    (h2n : (0:ℝ) < 2^n) (h1 : (a:ℝ)/2^n < x) (h2 : x ≤ ((b:ℝ)+1)/2^n) : a ≤ b := by
  have e1 : (a:ℝ) < x * 2^n := (div_lt_iff₀ h2n).mp h1
  have e2 : x * 2^n ≤ (b:ℝ) + 1 := (le_div_iff₀ h2n).mp h2
  have h3 : (a:ℝ) < (b:ℝ) + 1 := by linarith
  have h4 : a < b + 1 := by exact_mod_cast h3
  omega

lemma int_le_of_div_le_lt {n : ℕ} {a b : ℤ} {x : ℝ}
    (h2n : (0:ℝ) < 2^n) (h1 : (b:ℝ)/2^n ≤ x) (h2 : x < ((a:ℝ)+1)/2^n) : b ≤ a := by
  have e1 : (b:ℝ) ≤ x * 2^n := (div_le_iff₀ h2n).mp h1
  have e2 : x * 2^n < (a:ℝ) + 1 := (lt_div_iff₀ h2n).mp h2
  have h3 : (b:ℝ) < (a:ℝ) + 1 := by linarith
  have h4 : b < a + 1 := by exact_mod_cast h3
  omega

lemma int_le_succ_of_div_le_le {n : ℕ} {a b : ℤ} {x : ℝ}
    (h2n : (0:ℝ) < 2^n) (h1 : (a:ℝ)/2^n ≤ x) (h2 : x ≤ ((b:ℝ)+1)/2^n) : a ≤ b + 1 := by
  have e1 : (a:ℝ) ≤ x * 2^n := (div_le_iff₀ h2n).mp h1
  have e2 : x * 2^n ≤ (b:ℝ) + 1 := (le_div_iff₀ h2n).mp h2
  have h3 : (a:ℝ) ≤ (b:ℝ) + 1 := by linarith
  have h4 : a ≤ b + 1 := by exact_mod_cast h3
  exact h4

lemma eq_of_mem_dInt_dSq {n : ℕ} {q p : ℤ × ℤ} {z : ℂ}
    (hq : z ∈ dInt n q) (hp : z ∈ dSq n p) : q = p := by
  obtain ⟨hq1,hq2,hq3,hq4⟩ := hq
  obtain ⟨hp1,hp2,hp3,hp4⟩ := hp
  have h2n : (0:ℝ) < 2^n := by positivity
  have h1 : q.1 = p.1 := le_antisymm
    (int_le_of_div_lt_le h2n hq1 hp2) (int_le_of_div_le_lt h2n hp1 hq2)
  have h2 : q.2 = p.2 := le_antisymm
    (int_le_of_div_lt_le h2n hq3 hp4) (int_le_of_div_le_lt h2n hp3 hq4)
  exact Prod.ext h1 h2

lemma mem_dOpenTop_inter_dSq {n : ℕ} {q p : ℤ × ℤ} {z : ℂ}
    (hq : z ∈ dOpenTop n q) (hp : z ∈ dSq n p) : q = p ∨ q = (p.1, p.2 - 1) := by
  obtain ⟨hq1,hq2,hq3⟩ := hq
  obtain ⟨hp1,hp2,hp3,hp4⟩ := hp
  have h2n : (0:ℝ) < 2^n := by positivity
  have h1 : q.1 = p.1 := le_antisymm
    (int_le_of_div_lt_le h2n hq1 hp2) (int_le_of_div_le_lt h2n hp1 hq2)
  have him_ge : p.2 ≤ q.2 + 1 := by
    have e1 : (p.2:ℝ) ≤ z.im * 2^n := (div_le_iff₀ h2n).mp hp3
    have e2 : z.im * 2^n = (q.2:ℝ) + 1 := by
      rw [hq3, div_mul_cancel₀ _ (ne_of_gt h2n)]
    have : (p.2:ℝ) ≤ (q.2:ℝ) + 1 := by linarith
    exact_mod_cast this
  have him_le : q.2 + 1 ≤ p.2 + 1 := by
    have e1 : z.im * 2^n = (q.2:ℝ) + 1 := by
      rw [hq3, div_mul_cancel₀ _ (ne_of_gt h2n)]
    have e2 : z.im * 2^n ≤ (p.2:ℝ) + 1 := (le_div_iff₀ h2n).mp hp4
    have : (q.2:ℝ) + 1 ≤ (p.2:ℝ) + 1 := by linarith
    exact_mod_cast this
  rcases eq_or_lt_of_le him_ge with h | h
  · exact Or.inr (Prod.ext h1 (by omega))
  · exact Or.inl (Prod.ext h1 (by omega))

lemma dRemoved_inter_dSq_eq_empty {n : ℕ} {q p : ℤ × ℤ} (hq : q ≠ p)
    (hd : q ≠ (p.1, p.2 - 1)) : dRemoved n q ∩ dSq n p = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzq | hzq, hzp⟩
  · exact hq (eq_of_mem_dInt_dSq hzq hzp)
  · rcases mem_dOpenTop_inter_dSq hzq hzp with h | h
    · exact hq h
    · exact hd h


open scoped unitInterval

lemma dOpenTop_subset_dSq (n : ℕ) (p : ℤ × ℤ) : dOpenTop n p ⊆ dSq n p := by
  rintro z ⟨h1,h2,h3⟩
  have e : (p.2:ℝ)/2^n ≤ ((p.2:ℝ)+1)/2^n :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  refine ⟨le_of_lt h1, le_of_lt h2, ?_, ?_⟩ <;> rw [h3] <;> exact e

lemma dRemoved_subset_dSq (n : ℕ) (p : ℤ × ℤ) : dRemoved n p ⊆ dSq n p := by
  rintro z (h | h)
  · exact dInt_subset_dSq n p h
  · exact dOpenTop_subset_dSq n p h

lemma isClosed_dSq (n : ℕ) (p : ℤ × ℤ) : IsClosed (dSq n p) := by
  have h : dSq n p = (fun z : ℂ => (z.re, z.im)) ⁻¹'
      (Set.Icc ((p.1:ℝ)/2^n) (((p.1:ℝ)+1)/2^n) ×ˢ
       Set.Icc ((p.2:ℝ)/2^n) (((p.2:ℝ)+1)/2^n)) := by
    ext z; simp only [dSq, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Icc]; tauto
  rw [h]
  exact (isClosed_Icc.prod isClosed_Icc).preimage (by fun_prop)

lemma YSet_insert_eq (n : ℕ) (S A : Finset (ℤ × ℤ)) (p : ℤ × ℤ) :
    YSet n S (insert p A) = YSet n S A \ dRemoved n p := by
  ext z
  simp only [YSet, Set.mem_sdiff, Set.mem_iUnion]
  constructor
  · rintro ⟨hzK, hznot⟩
    refine ⟨⟨hzK, ?_⟩, ?_⟩
    · rintro ⟨q, hq, hzq⟩
      exact hznot ⟨q, Finset.mem_insert_of_mem hq, hzq⟩
    · intro hzp
      exact hznot ⟨p, Finset.mem_insert_self p A, hzp⟩
  · rintro ⟨⟨hzK, hznotA⟩, hzpnot⟩
    refine ⟨hzK, ?_⟩
    rintro ⟨q, hq, hzq⟩
    rcases Finset.mem_insert.mp hq with rfl | hqA
    · exact hzpnot hzq
    · exact hznotA ⟨q, hqA, hzq⟩

lemma YSet_insert_subset (n : ℕ) (S A : Finset (ℤ × ℤ)) (p : ℤ × ℤ) :
    YSet n S (insert p A) ⊆ YSet n S A := by
  rw [YSet_insert_eq]; exact Set.sdiff_subset

theorem step_retract {n : ℕ} {S A : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (fd : DFold n p)
    (hpS : p ∈ S) (hpA : p ∉ A)
    (hval : ∀ q ∈ A, (q.1, q.2+1) ∈ S → (q.1, q.2+1) ∈ A)
    (hup : (p.1, p.2+1) ∈ S → (p.1, p.2+1) ∈ A) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(YSet n S A) ↥(YSet n S (insert p A))) := by
  have hEqdown : ((p.1, p.2-1).1, (p.1, p.2-1).2 + 1) = p := by
    simp only [Prod.fst, Prod.snd]; exact Prod.ext rfl (by omega)
  have hdn : (p.1, p.2 - 1) ∉ A := by
    intro hmem
    have hps : ((p.1, p.2-1).1, (p.1, p.2-1).2 + 1) ∈ S := by rw [hEqdown]; exact hpS
    have hmem' := hval (p.1, p.2-1) hmem hps
    rw [hEqdown] at hmem'
    exact hpA hmem'
  have hnotRemoved : ∀ {q : ℤ × ℤ} {z : ℂ}, q ∈ A → z ∈ dSq n p → z ∉ dRemoved n q := by
    intro q z hqA hzp hzq
    have hqne : q ≠ p := by rintro rfl; exact hpA hqA
    have hdne : q ≠ (p.1, p.2 - 1) := by rintro rfl; exact hdn hqA
    have hmem : z ∈ dRemoved n q ∩ dSq n p := ⟨hzq, hzp⟩
    rw [dRemoved_inter_dSq_eq_empty hqne hdne] at hmem
    exact hmem
  have hSqA : dSq n p ⊆ YSet n S A := by
    intro z hz
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_iUnion]; exact ⟨p, hpS, hz⟩
    · simp only [Set.mem_iUnion]; rintro ⟨q, hqA, hzq⟩
      exact hnotRemoved hqA hz hzq
  have hmemH : ∀ z ∈ YSet n S A, ∀ t : unitInterval, fd.H (z, t) ∈ YSet n S A := by
    intro z hz t
    by_cases hzp : z ∈ dSq n p
    · have hH : fd.H (z, t) ∈ dSq n p := fd.Hmem z hzp t
      refine ⟨?_, ?_⟩
      · simp only [Set.mem_iUnion]; exact ⟨p, hpS, hH⟩
      · simp only [Set.mem_iUnion]; rintro ⟨q, hqA, hzq⟩
        exact hnotRemoved hqA hH hzq
    · rw [fd.Hout z hzp t]; exact hz
  have hImg : ∀ z ∈ YSet n S A, fd.φ z ∈ YSet n S (insert p A) := by
    intro z hz
    rw [YSet_insert_eq]
    by_cases hzp : z ∈ dSq n p
    · have hφ : fd.φ z ∈ dCore n p := fd.φmem z hzp
      have hφsq : fd.φ z ∈ dSq n p := hφ.1
      have hφnot : fd.φ z ∉ dRemoved n p := hφ.2
      refine ⟨⟨?_, ?_⟩, hφnot⟩
      · simp only [Set.mem_iUnion]; exact ⟨p, hpS, hφsq⟩
      · simp only [Set.mem_iUnion]; rintro ⟨q, hqA, hzq⟩
        exact hnotRemoved hqA hφsq hzq
    · rw [fd.φout z hzp]
      exact ⟨hz, fun h => hzp (dRemoved_subset_dSq n p h)⟩
  have hfix : ∀ z ∈ YSet n S (insert p A), ∀ t : unitInterval, fd.H (z, t) = z := by
    intro z hz t
    rw [YSet_insert_eq] at hz
    by_cases hzp : z ∈ dSq n p
    · exact fd.Hfix z ⟨hzp, hz.2⟩ t
    · exact fd.Hout z hzp t
  have hcont : Continuous (fun q : ↥(YSet n S A) × unitInterval => fd.H (q.1, q.2)) := by
    have hC1c : IsClosed {q : ↥(YSet n S A) × unitInterval | (q.1 : ℂ) ∈ dSq n p} :=
      IsClosed.preimage (continuous_subtype_val.comp continuous_fst) (isClosed_dSq n p)
    have hC2c : IsClosed {q : ↥(YSet n S A) × unitInterval | (q.1 : ℂ) ∉ dN n p} :=
      IsClosed.preimage (continuous_subtype_val.comp continuous_fst) (isOpen_dN n p).isClosed_compl
    have hcover : {q : ↥(YSet n S A) × unitInterval | (q.1 : ℂ) ∈ dSq n p} ∪
        {q : ↥(YSet n S A) × unitInterval | (q.1 : ℂ) ∉ dN n p} = Set.univ := by
      ext q; simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      by_cases h : (q.1 : ℂ) ∈ dN n p
      · left; exact mem_dSq_of_mem_YSet_dN hup q.1.2 h
      · right; exact h
    have hψ : Continuous (fun q : ↥(YSet n S A) × unitInterval => ((q.1 : ℂ), q.2)) :=
      continuous_prodMk.mpr ⟨continuous_subtype_val.comp continuous_fst, continuous_snd⟩
    have h1 : ContinuousOn (fun q : ↥(YSet n S A) × unitInterval => fd.H (q.1, q.2))
        {q : ↥(YSet n S A) × unitInterval | (q.1 : ℂ) ∈ dSq n p} := by
      refine fd.contH.comp hψ.continuousOn ?_
      intro q hq; exact ⟨hq, Set.mem_univ _⟩
    have heq2 : ∀ q ∈ {q : ↥(YSet n S A) × unitInterval | (q.1 : ℂ) ∉ dN n p},
        fd.H (q.1, q.2) = (q.1 : ℂ) := by
      intro q hq
      by_cases h : (q.1 : ℂ) ∈ dSq n p
      · exact fd.Hfix _ ⟨h, fun hc => hc.elim (fun hh => hq (dInt_subset_dN n p hh))
            (fun hh => hq (dOpenTop_subset_dN n p hh))⟩ q.2
      · exact fd.Hout _ h q.2
    have h2 : ContinuousOn (fun q : ↥(YSet n S A) × unitInterval => fd.H (q.1, q.2))
        {q : ↥(YSet n S A) × unitInterval | (q.1 : ℂ) ∉ dN n p} :=
      ContinuousOn.congr ((continuous_subtype_val.comp continuous_fst).continuousOn) heq2
    have huni := h1.union_of_isClosed h2 hC1c hC2c
    rw [hcover, continuousOn_univ] at huni
    exact huni
  set ρ : ↥(YSet n S A) × unitInterval → ↥(YSet n S A) :=
    fun q => ⟨fd.H (q.1, q.2), hmemH q.1 q.1.2 q.2⟩ with hρdef
  have hρcont : Continuous ρ := Continuous.subtype_mk hcont _
  have hρ0 : ∀ z : ↥(YSet n S A), ρ (z, (0:unitInterval)) = z := by
    intro z; apply Subtype.ext; show fd.H ((z:ℂ), (0:unitInterval)) = (z:ℂ)
    by_cases hzp : (z:ℂ) ∈ dSq n p
    · rw [fd.Hzero z hzp]
    · rw [fd.Hout z hzp]
  let C : Set ↥(YSet n S A) := {w | (w:ℂ) ∈ YSet n S (insert p A)}
  have hρ1 : ∀ z : ↥(YSet n S A), ρ (z, (1:unitInterval)) ∈ C := by
    intro z
    have hev : (ρ (z, (1:unitInterval)) : ℂ) = fd.φ (z:ℂ) := by
      show fd.H ((z:ℂ), (1:unitInterval)) = fd.φ (z:ℂ)
      by_cases hzp : (z:ℂ) ∈ dSq n p
      · exact fd.Hone z hzp
      · rw [fd.Hout z hzp, fd.φout z hzp]
    change ((ρ (z, (1:unitInterval)) : ↥(YSet n S A)) : ℂ) ∈ YSet n S (insert p A)
    rw [hev]; exact hImg z z.2
  have hρfix : ∀ z : ↥(YSet n S A), z ∈ C → ∀ t : unitInterval, ρ (z, t) = z := by
    intro z hz t; apply Subtype.ext; show fd.H ((z:ℂ), t) = (z:ℂ); exact hfix z hz t
  obtain ⟨e⟩ := Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract
    (X := ↥(YSet n S A)) (C := C) ρ hρcont hρ0 hρ1 hρfix
  have hhomeo : ↥C ≃ₜ ↥(YSet n S (insert p A)) :=
    { toFun := fun w => ⟨(w:ℂ), w.2⟩
      invFun := fun w => ⟨⟨(w:ℂ), YSet_insert_subset n S A p w.2⟩, w.2⟩
      left_inv := fun w => Subtype.ext rfl
      right_inv := fun w => Subtype.ext rfl
      continuous_toFun := Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val) _
      continuous_invFun := by
        have h1 : Continuous (fun w : ↥(YSet n S (insert p A)) =>
            (⟨(w:ℂ), YSet_insert_subset n S A p w.2⟩ : ↥(YSet n S A))) :=
          Continuous.subtype_mk (f := fun w : ↥(YSet n S (insert p A)) => (w:ℂ))
            continuous_subtype_val _
        show Continuous (fun w : ↥(YSet n S (insert p A)) =>
          (⟨(⟨(w:ℂ), YSet_insert_subset n S A p w.2⟩ : ↥(YSet n S A)), w.2⟩ : ↥C))
        exact Continuous.subtype_mk h1 _ }
  exact ⟨e.trans hhomeo.toHomotopyEquiv⟩


/-- The key ordering the squares are processed in: larger imaginary index first, then smaller
real index. -/

def sqKey (p : ℤ × ℤ) : Lex (ℤ × ℤ) := toLex (-p.2, p.1)

lemma sqKey_up_lt (p : ℤ × ℤ) : sqKey (p.1, p.2 + 1) < sqKey p := by
  simp only [sqKey, Prod.Lex.toLex_lt_toLex]
  omega


theorem yset_chain (n : ℕ) (S : Finset (ℤ × ℤ)) (fold : ∀ q : ℤ × ℤ, DFold n q)
    (A : Finset (ℤ × ℤ)) (hAS : A ⊆ S)
    (hval : ∀ q ∈ A, (q.1, q.2+1) ∈ S → (q.1, q.2+1) ∈ A) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(YSet n S A) ↥(YSet n S S)) := by
  classical
  have main : ∀ k, ∀ A : Finset (ℤ × ℤ), A ⊆ S →
      (∀ q ∈ A, (q.1, q.2+1) ∈ S → (q.1, q.2+1) ∈ A) → (S \ A).card = k →
      Nonempty (ContinuousMap.HomotopyEquiv ↥(YSet n S A) ↥(YSet n S S)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro A hAS hval hcard
      rcases Finset.eq_empty_or_nonempty (S \ A) with hemp | hne
      · have hsub : S ⊆ A := by
          intro x hxS
          by_contra hxA
          have hmem : x ∈ S \ A := Finset.mem_sdiff.mpr ⟨hxS, hxA⟩
          rw [hemp] at hmem
          exact (Finset.notMem_empty x) hmem
        have hAe : A = S := Finset.Subset.antisymm hAS hsub
        rw [hAe]
        exact ⟨ContinuousMap.HomotopyEquiv.refl _⟩
      · obtain ⟨p, hpB, hpmin⟩ := Finset.exists_min_image (S \ A) sqKey hne
        obtain ⟨hpS, hpA⟩ := Finset.mem_sdiff.mp hpB
        have hup : (p.1, p.2+1) ∈ S → (p.1, p.2+1) ∈ A := by
          intro hupS
          by_contra hupA
          have hmem : (p.1, p.2+1) ∈ S \ A := Finset.mem_sdiff.mpr ⟨hupS, hupA⟩
          have h1 := hpmin _ hmem
          have h2 := sqKey_up_lt p
          exact absurd h1 (not_le.mpr h2)
        have hval' : ∀ q ∈ insert p A, (q.1, q.2+1) ∈ S → (q.1, q.2+1) ∈ insert p A := by
          intro q hq hqS
          rcases Finset.mem_insert.mp hq with rfl | hqA
          · exact Finset.mem_insert_of_mem (hup hqS)
          · by_cases hqup : (q.1, q.2+1) = p
            · rw [hqup]; simp
            · exact Finset.mem_insert_of_mem (hval q hqA hqS)
        have herase : (S \ A).erase p = S \ insert p A := by
          ext x
          simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hxp, hxS, hxA⟩
            exact ⟨hxS, fun h => h.elim (fun h => hxp h) hxA⟩
          · rintro ⟨hxS, hx⟩
            refine ⟨?_, hxS, fun hxA => hx (Or.inr hxA)⟩
            rintro rfl; exact hx (Or.inl rfl)
        have hcard'' : (S \ A).card = (S \ insert p A).card + 1 := by
          rw [← herase, Finset.card_erase_of_mem hpB]
          exact (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨p, hpB⟩)).symm
        have hcard' : (S \ insert p A).card < k := by rw [← hcard, hcard'']; omega
        obtain ⟨e1⟩ := step_retract (fold p) hpS hpA hval hup
        obtain ⟨e2⟩ := ih (S \ insert p A).card hcard' (insert p A)
          (Finset.insert_subset_iff.mpr ⟨hpS, hAS⟩) hval' rfl
        exact ⟨e1.trans e2⟩
  exact main (S \ A).card A hAS hval rfl


-- begin geometry-added
lemma lineMap_re (x y : ℂ) (s : ℝ) :
    (AffineMap.lineMap x y s).re = (1 - s) * x.re + s * y.re := by
  rw [AffineMap.lineMap_apply_module (k := ℝ), Complex.real_smul, Complex.real_smul]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma lineMap_im (x y : ℂ) (s : ℝ) :
    (AffineMap.lineMap x y s).im = (1 - s) * x.im + s * y.im := by
  rw [AffineMap.lineMap_apply_module (k := ℝ), Complex.real_smul, Complex.real_smul]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma segment_vertical {a b c : ℝ} (hbc : b ≤ c) (z : ℂ) :
    z ∈ segment ℝ (⟨a, b⟩ : ℂ) ⟨a, c⟩ ↔ z.re = a ∧ b ≤ z.im ∧ z.im ≤ c := by
  constructor
  · intro hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    rw [lineMap_re, lineMap_im]
    refine ⟨by ring, by nlinarith [hs.1], by nlinarith [hs.2]⟩
  · rintro ⟨hre, hb, hc⟩
    rcases eq_or_lt_of_le hbc with h | h
    · have hz : z = (⟨a, b⟩ : ℂ) := by
        apply Complex.ext
        · simpa using hre
        · exact le_antisymm (h ▸ hc) hb
      rw [hz]
      exact left_mem_segment ℝ _ _
    · rw [segment_eq_image_lineMap]
      refine ⟨(z.im - b) / (c - b), ⟨⟨?_, ?_⟩, ?_⟩⟩
      · exact div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]; linarith
      · apply Complex.ext
        · rw [lineMap_re, hre]; field_simp; ring
        · rw [lineMap_im]; field_simp; ring

lemma segment_horizontal {a b c : ℝ} (hab : a ≤ c) (z : ℂ) :
    z ∈ segment ℝ (⟨a, b⟩ : ℂ) ⟨c, b⟩ ↔ z.im = b ∧ a ≤ z.re ∧ z.re ≤ c := by
  constructor
  · intro hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    rw [lineMap_re, lineMap_im]
    refine ⟨by ring, by nlinarith [hs.1], by nlinarith [hs.2]⟩
  · rintro ⟨him, ha, hc⟩
    rcases eq_or_lt_of_le hab with h | h
    · have hz : z = (⟨a, b⟩ : ℂ) := by
        apply Complex.ext
        · exact le_antisymm (h ▸ hc) ha
        · simpa using him
      rw [hz]
      exact left_mem_segment ℝ _ _
    · rw [segment_eq_image_lineMap]
      refine ⟨(z.re - a) / (c - a), ⟨⟨?_, ?_⟩, ?_⟩⟩
      · exact div_nonneg (by linarith) (by linarith)
      · rw [div_le_one (by linarith)]; linarith
      · apply Complex.ext
        · rw [lineMap_re]; field_simp; ring
        · rw [lineMap_im, him]; field_simp; ring

def gcorner (n : ℕ) (a b : ℤ) : ℂ := ⟨(a:ℝ)/2^n, (b:ℝ)/2^n⟩

lemma gcorner_re (n : ℕ) (a b : ℤ) : (gcorner n a b).re = (a:ℝ)/2^n := rfl
lemma gcorner_im (n : ℕ) (a b : ℤ) : (gcorner n a b).im = (b:ℝ)/2^n := rfl

lemma gcorner_inj {n : ℕ} {a b c d : ℤ} (h : gcorner n a b = gcorner n c d) :
    a = c ∧ b = d := by
  have h2n : ((2:ℝ)^n) ≠ 0 := by positivity
  have h1 : (a:ℝ)/2^n = (c:ℝ)/2^n := by rw [← gcorner_re, ← gcorner_re, h]
  have h2 : (b:ℝ)/2^n = (d:ℝ)/2^n := by rw [← gcorner_im, ← gcorner_im, h]
  constructor
  · have : (a:ℝ) = (c:ℝ) := by
      rw [div_eq_div_iff h2n h2n] at h1; exact mul_right_cancel₀ h2n h1
    exact_mod_cast this
  · have : (b:ℝ) = (d:ℝ) := by
      rw [div_eq_div_iff h2n h2n] at h2; exact mul_right_cancel₀ h2n h2
    exact_mod_cast this

lemma gcorner_ext {n : ℕ} {a b : ℤ} {z : ℂ} (hre : z.re = (a:ℝ)/2^n)
    (him : z.im = (b:ℝ)/2^n) : z = gcorner n a b := by
  apply Complex.ext <;> simp [gcorner, hre, him]

lemma mem_vSeg {n : ℕ} {a b : ℤ} {z : ℂ} :
    z ∈ segment ℝ (gcorner n a b) (gcorner n a (b+1)) ↔
      z.re = (a:ℝ)/2^n ∧ (b:ℝ)/2^n ≤ z.im ∧ z.im ≤ ((b:ℝ)+1)/2^n := by
  have h2 : gcorner n a (b+1) = (⟨(a:ℝ)/2^n, ((b:ℝ)+1)/2^n⟩ : ℂ) := by
    apply Complex.ext <;> simp [gcorner]
  have hle : (b:ℝ)/2^n ≤ ((b:ℝ)+1)/2^n := by
    rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 2^n)]; linarith
  rw [show gcorner n a b = (⟨(a:ℝ)/2^n, (b:ℝ)/2^n⟩ : ℂ) from rfl, h2, segment_vertical hle]

lemma mem_hSeg {n : ℕ} {a b : ℤ} {z : ℂ} :
    z ∈ segment ℝ (gcorner n a b) (gcorner n (a+1) b) ↔
      z.im = (b:ℝ)/2^n ∧ (a:ℝ)/2^n ≤ z.re ∧ z.re ≤ ((a:ℝ)+1)/2^n := by
  have h2 : gcorner n (a+1) b = (⟨((a:ℝ)+1)/2^n, (b:ℝ)/2^n⟩ : ℂ) := by
    apply Complex.ext <;> simp [gcorner]
  have hle : (a:ℝ)/2^n ≤ ((a:ℝ)+1)/2^n := by
    rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 2^n)]; linarith
  rw [show gcorner n a b = (⟨(a:ℝ)/2^n, (b:ℝ)/2^n⟩ : ℂ) from rfl, h2, segment_horizontal hle]

lemma gridSeg_vSeg_inter_vSeg {n : ℕ} {a b a' b' : ℤ} (h : (a, b) ≠ (a', b')) :
    segment ℝ (gcorner n a b) (gcorner n a (b+1)) ∩
      segment ℝ (gcorner n a' b') (gcorner n a' (b'+1)) ⊆
      ({gcorner n a b, gcorner n a (b+1)} : Set ℂ) ∩
      ({gcorner n a' b', gcorner n a' (b'+1)} : Set ℂ) := by
  rintro z ⟨hz, hz'⟩
  rw [mem_vSeg] at hz hz'
  obtain ⟨hzre, hzb, hzc⟩ := hz
  obtain ⟨hzre', hzb', hzc'⟩ := hz'
  have h2n : (0:ℝ) < 2^n := by positivity
  have h2nne : ((2:ℝ)^n) ≠ 0 := ne_of_gt h2n
  have a1 : (b:ℝ) ≤ z.im * 2^n := (div_le_iff₀ h2n).mp hzb
  have a2 : z.im * 2^n ≤ (b:ℝ) + 1 := (le_div_iff₀ h2n).mp hzc
  have a1' : (b':ℝ) ≤ z.im * 2^n := (div_le_iff₀ h2n).mp hzb'
  have a2' : z.im * 2^n ≤ (b':ℝ) + 1 := (le_div_iff₀ h2n).mp hzc'
  have haa : a = a' := by
    have h1 : (a:ℝ)/2^n = (a':ℝ)/2^n := by rw [← hzre, ← hzre']
    rw [div_eq_div_iff h2nne h2nne] at h1
    exact_mod_cast mul_right_cancel₀ h2nne h1
  have hbb : b ≠ b' := fun hbb' => h (Prod.ext haa hbb')
  rcases lt_or_gt_of_ne hbb with hlt | hlt
  · have hle : (b:ℝ) + 1 ≤ (b':ℝ) := by exact_mod_cast (by omega : b + 1 ≤ b')
    have ht : z.im * 2^n = (b:ℝ) + 1 := by linarith
    have hb' : b + 1 = b' := by
      have : (b:ℝ) + 1 = (b':ℝ) := le_antisymm hle (by linarith)
      exact_mod_cast this
    have hzim : z.im = ((b:ℝ)+1)/2^n := (eq_div_iff h2nne).mpr ht
    have hzim' : z.im = (((b+1 : ℤ)):ℝ)/2^n := by push_cast; exact hzim
    have hzeq : z = gcorner n a (b+1) := gcorner_ext hzre hzim'
    have hzeq' : z = gcorner n a' b' :=
      gcorner_ext (by rw [← haa]; exact hzre) (by rw [← hb']; push_cast; exact hzim)
    refine ⟨?_, ?_⟩
    · rw [hzeq]; exact Or.inr rfl
    · rw [hzeq']; exact Or.inl rfl
  · have hle : (b':ℝ) + 1 ≤ (b:ℝ) := by exact_mod_cast (by omega : b' + 1 ≤ b)
    have ht : z.im * 2^n = (b':ℝ) + 1 := by linarith
    have hb' : b' + 1 = b := by
      have : (b':ℝ) + 1 = (b:ℝ) := le_antisymm hle (by linarith)
      exact_mod_cast this
    have hzim' : z.im = (((b'+1 : ℤ)):ℝ)/2^n := (eq_div_iff h2nne).mpr (by push_cast; exact ht)
    have hzim : z.im = (b:ℝ)/2^n := by rw [hzim', ← hb']
    have hzeq : z = gcorner n a b := gcorner_ext hzre hzim
    have hzeq' : z = gcorner n a' (b'+1) := gcorner_ext (by rw [← haa]; exact hzre) hzim'
    refine ⟨?_, ?_⟩
    · rw [hzeq]; exact Or.inl rfl
    · rw [hzeq']; exact Or.inr rfl

lemma gridSeg_vSeg_inter_hSeg {n : ℕ} {a b a' b' : ℤ} :
    segment ℝ (gcorner n a b) (gcorner n a (b+1)) ∩
      segment ℝ (gcorner n a' b') (gcorner n (a'+1) b') ⊆
      ({gcorner n a b, gcorner n a (b+1)} : Set ℂ) ∩
      ({gcorner n a' b', gcorner n (a'+1) b'} : Set ℂ) := by
  rintro z ⟨hz, hz'⟩
  rw [mem_vSeg] at hz
  rw [mem_hSeg] at hz'
  obtain ⟨hzre, hzb, hzc⟩ := hz
  obtain ⟨hzim, hza, hza'⟩ := hz'
  have h2n : (0:ℝ) < 2^n := by positivity
  have h2nne : ((2:ℝ)^n) ≠ 0 := ne_of_gt h2n
  have hb' : b' = b ∨ b' = b + 1 := by
    have e1 : (b:ℝ) ≤ (b':ℝ) := by
      have h : (b:ℝ) ≤ z.im * 2^n := (div_le_iff₀ h2n).mp hzb
      rw [hzim, div_mul_cancel₀ _ h2nne] at h
      exact h
    have e2 : (b':ℝ) ≤ (b:ℝ) + 1 := by
      have h : z.im * 2^n ≤ (b:ℝ) + 1 := (le_div_iff₀ h2n).mp hzc
      rw [hzim, div_mul_cancel₀ _ h2nne] at h
      exact h
    have h1 : b ≤ b' := by exact_mod_cast e1
    have h2 : b' ≤ b + 1 := by exact_mod_cast e2
    omega
  have ha' : a = a' ∨ a = a' + 1 := by
    have e1 : (a':ℝ) ≤ (a:ℝ) := by
      have h : (a':ℝ) ≤ z.re * 2^n := (div_le_iff₀ h2n).mp hza
      rw [hzre, div_mul_cancel₀ _ h2nne] at h
      exact h
    have e2 : (a:ℝ) ≤ (a':ℝ) + 1 := by
      have h : z.re * 2^n ≤ (a':ℝ) + 1 := (le_div_iff₀ h2n).mp hza'
      rw [hzre, div_mul_cancel₀ _ h2nne] at h
      exact h
    have h1 : a' ≤ a := by exact_mod_cast e1
    have h2 : a ≤ a' + 1 := by exact_mod_cast e2
    omega
  have hzeq : z = gcorner n a b' := gcorner_ext hzre hzim
  refine ⟨?_, ?_⟩
  · rcases hb' with h | h
    · rw [hzeq, h]; exact Or.inl rfl
    · rw [hzeq, h]; exact Or.inr rfl
  · rcases ha' with h | h
    · rw [hzeq, h]; exact Or.inl rfl
    · rw [hzeq, h]; exact Or.inr rfl

lemma gridSeg_hSeg_inter_hSeg {n : ℕ} {a b a' b' : ℤ} (h : (a, b) ≠ (a', b')) :
    segment ℝ (gcorner n a b) (gcorner n (a+1) b) ∩
      segment ℝ (gcorner n a' b') (gcorner n (a'+1) b') ⊆
      ({gcorner n a b, gcorner n (a+1) b} : Set ℂ) ∩
      ({gcorner n a' b', gcorner n (a'+1) b'} : Set ℂ) := by
  rintro z ⟨hz, hz'⟩
  rw [mem_hSeg] at hz hz'
  obtain ⟨hzim, hza, hzc⟩ := hz
  obtain ⟨hzim', hza', hzc'⟩ := hz'
  have h2n : (0:ℝ) < 2^n := by positivity
  have h2nne : ((2:ℝ)^n) ≠ 0 := ne_of_gt h2n
  have a1 : (a:ℝ) ≤ z.re * 2^n := (div_le_iff₀ h2n).mp hza
  have a2 : z.re * 2^n ≤ (a:ℝ) + 1 := (le_div_iff₀ h2n).mp hzc
  have a1' : (a':ℝ) ≤ z.re * 2^n := (div_le_iff₀ h2n).mp hza'
  have a2' : z.re * 2^n ≤ (a':ℝ) + 1 := (le_div_iff₀ h2n).mp hzc'
  have hbb : b = b' := by
    have h1 : (b:ℝ)/2^n = (b':ℝ)/2^n := by rw [← hzim, ← hzim']
    rw [div_eq_div_iff h2nne h2nne] at h1
    exact_mod_cast mul_right_cancel₀ h2nne h1
  have haa : a ≠ a' := fun haa' => h (Prod.ext haa' hbb)
  rcases lt_or_gt_of_ne haa with hlt | hlt
  · have hle : (a:ℝ) + 1 ≤ (a':ℝ) := by exact_mod_cast (by omega : a + 1 ≤ a')
    have ht : z.re * 2^n = (a:ℝ) + 1 := by linarith
    have ha' : a + 1 = a' := by
      have : (a:ℝ) + 1 = (a':ℝ) := le_antisymm hle (by linarith)
      exact_mod_cast this
    have hzre : z.re = ((a:ℝ)+1)/2^n := (eq_div_iff h2nne).mpr ht
    have hzre' : z.re = (((a+1 : ℤ)):ℝ)/2^n := by push_cast; exact hzre
    have hzeq : z = gcorner n (a+1) b := gcorner_ext hzre' hzim
    have hzeq' : z = gcorner n a' b' :=
      gcorner_ext (by rw [← ha']; push_cast; exact hzre) (by rw [← hbb]; exact hzim)
    refine ⟨?_, ?_⟩
    · rw [hzeq]; exact Or.inr rfl
    · rw [hzeq']; exact Or.inl rfl
  · have hle : (a':ℝ) + 1 ≤ (a:ℝ) := by exact_mod_cast (by omega : a' + 1 ≤ a)
    have ht : z.re * 2^n = (a':ℝ) + 1 := by linarith
    have ha' : a' + 1 = a := by
      have : (a':ℝ) + 1 = (a:ℝ) := le_antisymm hle (by linarith)
      exact_mod_cast this
    have hzre' : z.re = (((a'+1 : ℤ)):ℝ)/2^n := (eq_div_iff h2nne).mpr (by push_cast; exact ht)
    have hzre : z.re = (a:ℝ)/2^n := by rw [hzre', ← ha']
    have hzeq : z = gcorner n a b := gcorner_ext hzre hzim
    have hzeq' : z = gcorner n (a'+1) b' := gcorner_ext hzre' (by rw [← hbb]; exact hzim)
    refine ⟨?_, ?_⟩
    · rw [hzeq]; exact Or.inl rfl
    · rw [hzeq']; exact Or.inr rfl


-- end geometry-added

lemma gridSeg_hSeg_inter_vSeg {n : ℕ} {a b a' b' : ℤ} :
    segment ℝ (gcorner n a b) (gcorner n (a+1) b) ∩
      segment ℝ (gcorner n a' b') (gcorner n a' (b'+1)) ⊆
      ({gcorner n a b, gcorner n (a+1) b} : Set ℂ) ∩
      ({gcorner n a' b', gcorner n a' (b'+1)} : Set ℂ) := by
  intro z hz
  have h := gridSeg_vSeg_inter_hSeg (n := n) (a := a') (b := b') (a' := a) (b' := b)
    ⟨hz.2, hz.1⟩
  exact ⟨h.2, h.1⟩

/-! ## The grid vertices and edges of a finite set of dyadic squares -/

def gVerts (n : ℕ) (S : Finset (ℤ × ℤ)) : Finset ℂ :=
  S.biUnion fun p => {gcorner n p.1 p.2, gcorner n (p.1+1) p.2, gcorner n p.1 (p.2+1),
                      gcorner n (p.1+1) (p.2+1)}

def gVEdges (n : ℕ) (S : Finset (ℤ × ℤ)) : Finset (ℂ × ℂ) :=
  (S.image fun p => (gcorner n p.1 p.2, gcorner n p.1 (p.2+1))) ∪
  (S.image fun p => (gcorner n (p.1+1) p.2, gcorner n (p.1+1) (p.2+1)))

def gHEdges (n : ℕ) (S : Finset (ℤ × ℤ)) : Finset (ℂ × ℂ) :=
  (S.filter fun p => (p.1, p.2-1) ∉ S).image fun p => (gcorner n p.1 p.2, gcorner n (p.1+1) p.2)

def gEdges (n : ℕ) (S : Finset (ℤ × ℤ)) : Finset (ℂ × ℂ) := gVEdges n S ∪ gHEdges n S

lemma mem_gVerts {n : ℕ} {S : Finset (ℤ × ℤ)} {v : ℂ} : v ∈ gVerts n S ↔
    ∃ p ∈ S, v = gcorner n p.1 p.2 ∨ v = gcorner n (p.1+1) p.2 ∨
             v = gcorner n p.1 (p.2+1) ∨ v = gcorner n (p.1+1) (p.2+1) := by
  rw [gVerts, Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, hv⟩
    exact ⟨p, hp, by simpa using hv⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, by simpa using h⟩

lemma mem_gVEdges {n : ℕ} {S : Finset (ℤ × ℤ)} {e : ℂ × ℂ} : e ∈ gVEdges n S ↔
    (∃ p ∈ S, (gcorner n p.1 p.2, gcorner n p.1 (p.2+1)) = e) ∨
    (∃ p ∈ S, (gcorner n (p.1+1) p.2, gcorner n (p.1+1) (p.2+1)) = e) := by
  rw [gVEdges, Finset.mem_union, Finset.mem_image, Finset.mem_image]

lemma mem_gHEdges {n : ℕ} {S : Finset (ℤ × ℤ)} {e : ℂ × ℂ} : e ∈ gHEdges n S ↔
    ∃ p ∈ S, (p.1, p.2-1) ∉ S ∧ (gcorner n p.1 p.2, gcorner n (p.1+1) p.2) = e := by
  rw [gHEdges, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, he⟩
    rw [Finset.mem_filter] at hp
    exact ⟨p, hp.1, hp.2, he⟩
  · rintro ⟨p, hp, hp', he⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hp'⟩, he⟩

lemma gVerts_corner₁ {n : ℕ} {S : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (hp : p ∈ S) :
    gcorner n p.1 p.2 ∈ gVerts n S :=
  mem_gVerts.mpr ⟨p, hp, Or.inl rfl⟩

lemma gVerts_corner₂ {n : ℕ} {S : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (hp : p ∈ S) :
    gcorner n (p.1+1) p.2 ∈ gVerts n S :=
  mem_gVerts.mpr ⟨p, hp, Or.inr (Or.inl rfl)⟩

lemma gVerts_corner₃ {n : ℕ} {S : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (hp : p ∈ S) :
    gcorner n p.1 (p.2+1) ∈ gVerts n S :=
  mem_gVerts.mpr ⟨p, hp, Or.inr (Or.inr (Or.inl rfl))⟩

lemma gVerts_corner₄ {n : ℕ} {S : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (hp : p ∈ S) :
    gcorner n (p.1+1) (p.2+1) ∈ gVerts n S :=
  mem_gVerts.mpr ⟨p, hp, Or.inr (Or.inr (Or.inr rfl))⟩

lemma pairs_eq {a b c d : ℤ} (h : (a, b) = (c, d)) : a = c ∧ b = d :=
  ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

lemma gEdges_endpoints_mem_gVerts {n : ℕ} {S : Finset (ℤ × ℤ)} {e : ℂ × ℂ}
    (he : e ∈ gEdges n S) : e.1 ∈ gVerts n S ∧ e.2 ∈ gVerts n S := by
  rcases Finset.mem_union.mp he with hv | hh
  · rcases mem_gVEdges.mp hv with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact ⟨gVerts_corner₁ hp, gVerts_corner₃ hp⟩
    · exact ⟨gVerts_corner₂ hp, gVerts_corner₄ hp⟩
  · rcases mem_gHEdges.mp hh with ⟨p, hp, -, rfl⟩
    exact ⟨gVerts_corner₁ hp, gVerts_corner₂ hp⟩

lemma gEdges_ne {n : ℕ} {S : Finset (ℤ × ℤ)} {e : ℂ × ℂ} (he : e ∈ gEdges n S) :
    e.1 ≠ e.2 := by
  rcases Finset.mem_union.mp he with hv | hh
  · rcases mem_gVEdges.mp hv with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · intro h; obtain ⟨-, h2⟩ := gcorner_inj h; omega
    · intro h; obtain ⟨-, h2⟩ := gcorner_inj h; omega
  · rcases mem_gHEdges.mp hh with ⟨p, hp, -, rfl⟩
    intro h; obtain ⟨h1, -⟩ := gcorner_inj h; omega

lemma gEdges_disjoint_segments {n : ℕ} {S : Finset (ℤ × ℤ)} {e e' : ℂ × ℂ}
    (he : e ∈ gEdges n S) (he' : e' ∈ gEdges n S) (hne : e ≠ e') :
    segment ℝ e.1 e.2 ∩ segment ℝ e'.1 e'.2 ⊆
      ({e.1, e.2} : Set ℂ) ∩ ({e'.1, e'.2} : Set ℂ) := by
  rcases Finset.mem_union.mp he with hv | hh
  · rcases mem_gVEdges.mp hv with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · rcases Finset.mem_union.mp he' with hv' | hh'
      · rcases mem_gVEdges.mp hv' with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · refine gridSeg_vSeg_inter_vSeg (fun hpq => ?_)
          obtain ⟨h1, h2⟩ := pairs_eq hpq; exact hne (by rw [h1, h2])
        · refine gridSeg_vSeg_inter_vSeg (fun hpq => ?_)
          obtain ⟨h1, h2⟩ := pairs_eq hpq; exact hne (by rw [h1, h2])
      · rcases mem_gHEdges.mp hh' with ⟨q, hq, -, rfl⟩
        exact gridSeg_vSeg_inter_hSeg
    · rcases Finset.mem_union.mp he' with hv' | hh'
      · rcases mem_gVEdges.mp hv' with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · refine gridSeg_vSeg_inter_vSeg (fun hpq => ?_)
          obtain ⟨h1, h2⟩ := pairs_eq hpq; exact hne (by rw [h1, h2])
        · refine gridSeg_vSeg_inter_vSeg (fun hpq => ?_)
          obtain ⟨h1, h2⟩ := pairs_eq hpq; exact hne (by rw [h1, h2])
      · rcases mem_gHEdges.mp hh' with ⟨q, hq, -, rfl⟩
        exact gridSeg_vSeg_inter_hSeg
  · rcases mem_gHEdges.mp hh with ⟨p, hp, hp', rfl⟩
    rcases Finset.mem_union.mp he' with hv' | hh'
    · rcases mem_gVEdges.mp hv' with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · exact gridSeg_hSeg_inter_vSeg
      · exact gridSeg_hSeg_inter_vSeg
    · rcases mem_gHEdges.mp hh' with ⟨q, hq, -, rfl⟩
      refine gridSeg_hSeg_inter_hSeg (fun hpq => ?_)
      obtain ⟨h1, h2⟩ := pairs_eq hpq; exact hne (by rw [h1, h2])


/-! ## The spine as a finite union of closed segments -/

lemma eq_or_eq_of_not_Ioo {a b x : ℝ} (h1 : a ≤ x) (h2 : x ≤ b)
    (h3 : ¬(a < x ∧ x < b)) : x = a ∨ x = b := by
  rcases not_and_or.mp h3 with h | h
  · exact Or.inl (le_antisymm (le_of_not_gt h) h1)
  · exact Or.inr (le_antisymm h2 (le_of_not_gt h))

lemma div_le_div_succ (n : ℕ) (a : ℤ) : (a:ℝ)/2^n ≤ ((a:ℝ)+1)/2^n :=
  div_le_div_of_nonneg_right (by linarith) (by positivity)

lemma cast_succ (a : ℤ) : (((a+1 : ℤ)):ℝ) = (a:ℝ) + 1 := by push_cast; ring

lemma gcorner_re_succ (n : ℕ) (a b : ℤ) : (gcorner n (a+1) b).re = ((a:ℝ)+1)/2^n := by
  rw [gcorner_re, cast_succ]

lemma gcorner_im_succ (n : ℕ) (a b : ℤ) : (gcorner n a (b+1)).im = ((b:ℝ)+1)/2^n := by
  rw [gcorner_im, cast_succ]

lemma dSq_corner {n : ℕ} {p : ℤ × ℤ} {z : ℂ}
    (hre : z.re = (p.1:ℝ)/2^n ∨ z.re = ((p.1:ℝ)+1)/2^n)
    (him : z.im = (p.2:ℝ)/2^n ∨ z.im = ((p.2:ℝ)+1)/2^n) : z ∈ dSq n p := by
  have hA := div_le_div_succ n p.1
  have hB := div_le_div_succ n p.2
  rcases hre with hre | hre <;> rcases him with him | him
  · exact ⟨le_of_eq hre.symm, (le_of_eq hre).trans hA, le_of_eq him.symm,
      (le_of_eq him).trans hB⟩
  · exact ⟨le_of_eq hre.symm, (le_of_eq hre).trans hA, hB.trans_eq him.symm, le_of_eq him⟩
  · exact ⟨hA.trans_eq hre.symm, le_of_eq hre, le_of_eq him.symm, (le_of_eq him).trans hB⟩
  · exact ⟨hA.trans_eq hre.symm, le_of_eq hre, hB.trans_eq him.symm, le_of_eq him⟩

lemma dSq_of_re_endpoint {n : ℕ} {p : ℤ × ℤ} {z : ℂ}
    (hre : z.re = (p.1:ℝ)/2^n ∨ z.re = ((p.1:ℝ)+1)/2^n)
    (h3 : (p.2:ℝ)/2^n ≤ z.im) (h4 : z.im ≤ ((p.2:ℝ)+1)/2^n) : z ∈ dSq n p := by
  have hA := div_le_div_succ n p.1
  rcases hre with hre | hre
  · exact ⟨le_of_eq hre.symm, (le_of_eq hre).trans hA, h3, h4⟩
  · exact ⟨hA.trans_eq hre.symm, le_of_eq hre, h3, h4⟩

lemma dSq_of_im_endpoint {n : ℕ} {p : ℤ × ℤ} {z : ℂ} (him : z.im = (p.2:ℝ)/2^n)
    (h1 : (p.1:ℝ)/2^n ≤ z.re) (h2 : z.re ≤ ((p.1:ℝ)+1)/2^n) : z ∈ dSq n p := by
  have hB := div_le_div_succ n p.2
  exact ⟨h1, h2, le_of_eq him.symm, (le_of_eq him).trans hB⟩

lemma mem_YSet_of_re_endpoint {n : ℕ} {S : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (hpS : p ∈ S)
    {z : ℂ} (hzsq : z ∈ dSq n p)
    (hre : z.re = (p.1:ℝ)/2^n ∨ z.re = ((p.1:ℝ)+1)/2^n) : z ∈ YSet n S S := by
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_iUnion]; exact ⟨p, hpS, hzsq⟩
  · simp only [Set.mem_iUnion]
    rintro ⟨q, hqS, hqrem⟩
    rcases hqrem with hdint | hdtop
    · have hqp : q = p := eq_of_mem_dInt_dSq hdint hzsq
      obtain ⟨h1, h2, -, -⟩ := hdint
      rw [hqp] at h1 h2
      rcases hre with h | h
      · exact absurd (h ▸ h1) (lt_irrefl _)
      · exact absurd (h ▸ h2) (lt_irrefl _)
    · have hqp : q = p ∨ q = (p.1, p.2-1) := mem_dOpenTop_inter_dSq hdtop hzsq
      obtain ⟨h1, h2, -⟩ := hdtop
      have hq1 : q.1 = p.1 := by rcases hqp with h | h <;> rw [h]
      rw [hq1] at h1 h2
      rcases hre with h | h
      · exact absurd (h ▸ h1) (lt_irrefl _)
      · exact absurd (h ▸ h2) (lt_irrefl _)

lemma mem_YSet_of_bottom_edge {n : ℕ} {S : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (hpS : p ∈ S)
    {z : ℂ} (hzsq : z ∈ dSq n p) (hbelow : (p.1, p.2-1) ∉ S)
    (him : z.im = (p.2:ℝ)/2^n) : z ∈ YSet n S S := by
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_iUnion]; exact ⟨p, hpS, hzsq⟩
  · simp only [Set.mem_iUnion]
    rintro ⟨q, hqS, hqrem⟩
    rcases hqrem with hdint | hdtop
    · have hqp : q = p := eq_of_mem_dInt_dSq hdint hzsq
      obtain ⟨-, -, h3, -⟩ := hdint
      rw [hqp] at h3
      exact absurd (him ▸ h3) (lt_irrefl _)
    · have hqp : q = p ∨ q = (p.1, p.2-1) := mem_dOpenTop_inter_dSq hdtop hzsq
      obtain ⟨-, -, h3⟩ := hdtop
      rcases hqp with hqp | hqp
      · rw [hqp] at h3
        rw [him] at h3
        have h2n : ((2:ℝ)^n) ≠ 0 := by positivity
        rw [div_eq_div_iff h2n h2n] at h3
        have : (p.2:ℝ) = (p.2:ℝ) + 1 := mul_right_cancel₀ h2n h3
        linarith
      · exact absurd (hqp ▸ hqS) hbelow

theorem YSet_eq_segments (n : ℕ) (S : Finset (ℤ × ℤ)) :
    YSet n S S = (gVerts n S : Set ℂ) ∪ ⋃ e ∈ gEdges n S, segment ℝ e.1 e.2 := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzK, hznot⟩ := hz
    have hznot' : ∀ q ∈ S, z ∉ dRemoved n q := by
      intro q hq hqrem
      exact hznot (by simp only [Set.mem_iUnion]; exact ⟨q, hq, hqrem⟩)
    obtain ⟨p, hpS, hzp⟩ := Set.mem_iUnion₂.mp hzK
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hzp
    have hb : z.re = (p.1:ℝ)/2^n ∨ z.re = ((p.1:ℝ)+1)/2^n ∨
              z.im = (p.2:ℝ)/2^n ∨ z.im = ((p.2:ℝ)+1)/2^n := by
      by_contra h
      push Not at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      exact hznot' p hpS (Or.inl ⟨lt_of_le_of_ne hz1 (Ne.symm h1), lt_of_le_of_ne hz2 h2,
        lt_of_le_of_ne hz3 (Ne.symm h3), lt_of_le_of_ne hz4 h4⟩)
    rcases hb with hre | hre | him | him
    · refine Or.inr (Set.mem_iUnion₂.mpr ⟨(gcorner n p.1 p.2, gcorner n p.1 (p.2+1)), ?_, ?_⟩)
      · exact Finset.mem_union_left _ (mem_gVEdges.mpr (Or.inl ⟨p, hpS, rfl⟩))
      · rw [mem_vSeg]; exact ⟨hre, hz3, hz4⟩
    · have hre' : z.re = (((p.1+1 : ℤ)):ℝ)/2^n := by rw [hre]; push_cast; ring
      refine Or.inr (Set.mem_iUnion₂.mpr
        ⟨(gcorner n (p.1+1) p.2, gcorner n (p.1+1) (p.2+1)), ?_, ?_⟩)
      · exact Finset.mem_union_left _ (mem_gVEdges.mpr (Or.inr ⟨p, hpS, rfl⟩))
      · rw [mem_vSeg]; exact ⟨hre', hz3, hz4⟩
    · by_cases hbelow : (p.1, p.2-1) ∈ S
      · have hnotd : z ∉ dOpenTop n (p.1, p.2-1) :=
          fun h => hznot' (p.1, p.2-1) hbelow (Or.inr h)
        have h3 : z.im = ((((p.2 - 1 : ℤ)):ℝ) + 1)/2^n := by
          rw [him]; push_cast; ring
        have hnot : ¬((p.1:ℝ)/2^n < z.re ∧ z.re < ((p.1:ℝ)+1)/2^n) :=
          fun hcon => hnotd ⟨hcon.1, hcon.2, h3⟩
        rcases eq_or_eq_of_not_Ioo hz1 hz2 hnot with hre | hre
        · have hzeq : z = gcorner n p.1 p.2 := gcorner_ext hre him
          rw [hzeq]; exact Or.inl (gVerts_corner₁ hpS)
        · have hre' : z.re = (((p.1+1 : ℤ)):ℝ)/2^n := by rw [hre]; push_cast; ring
          have hzeq : z = gcorner n (p.1+1) p.2 := gcorner_ext hre' him
          rw [hzeq]; exact Or.inl (gVerts_corner₂ hpS)
      · refine Or.inr (Set.mem_iUnion₂.mpr ⟨(gcorner n p.1 p.2, gcorner n (p.1+1) p.2), ?_, ?_⟩)
        · exact Finset.mem_union_right _ (mem_gHEdges.mpr ⟨p, hpS, hbelow, rfl⟩)
        · rw [mem_hSeg]; exact ⟨him, hz1, hz2⟩
    · have hnotd : z ∉ dOpenTop n p := fun h => hznot' p hpS (Or.inr h)
      have hnot : ¬((p.1:ℝ)/2^n < z.re ∧ z.re < ((p.1:ℝ)+1)/2^n) :=
        fun hcon => hnotd ⟨hcon.1, hcon.2, him⟩
      have him' : z.im = (((p.2+1 : ℤ)):ℝ)/2^n := by rw [him]; push_cast; ring
      rcases eq_or_eq_of_not_Ioo hz1 hz2 hnot with hre | hre
      · have hzeq : z = gcorner n p.1 (p.2+1) := gcorner_ext hre him'
        rw [hzeq]; exact Or.inl (gVerts_corner₃ hpS)
      · have hre' : z.re = (((p.1+1 : ℤ)):ℝ)/2^n := by rw [hre]; push_cast; ring
        have hzeq : z = gcorner n (p.1+1) (p.2+1) := gcorner_ext hre' him'
        rw [hzeq]; exact Or.inl (gVerts_corner₄ hpS)
  · intro hz
    rcases hz with hzV | hzE
    · rcases mem_gVerts.mp hzV with ⟨p, hpS, hv | hv | hv | hv⟩
      · rw [hv]
        have hzsq : gcorner n p.1 p.2 ∈ dSq n p :=
          dSq_corner (Or.inl (gcorner_re n p.1 p.2)) (Or.inl (gcorner_im n p.1 p.2))
        have hre : (gcorner n p.1 p.2).re = (p.1:ℝ)/2^n ∨
            (gcorner n p.1 p.2).re = ((p.1:ℝ)+1)/2^n := Or.inl (gcorner_re n p.1 p.2)
        exact mem_YSet_of_re_endpoint hpS hzsq hre
      · rw [hv]
        have hzsq : gcorner n (p.1+1) p.2 ∈ dSq n p :=
          dSq_corner (Or.inr (gcorner_re_succ n p.1 p.2)) (Or.inl (gcorner_im n p.1 p.2))
        have hre : (gcorner n (p.1+1) p.2).re = (p.1:ℝ)/2^n ∨
            (gcorner n (p.1+1) p.2).re = ((p.1:ℝ)+1)/2^n := Or.inr (gcorner_re_succ n p.1 p.2)
        exact mem_YSet_of_re_endpoint hpS hzsq hre
      · rw [hv]
        have hzsq : gcorner n p.1 (p.2+1) ∈ dSq n p :=
          dSq_corner (Or.inl (gcorner_re n p.1 (p.2+1))) (Or.inr (gcorner_im_succ n p.1 p.2))
        have hre : (gcorner n p.1 (p.2+1)).re = (p.1:ℝ)/2^n ∨
            (gcorner n p.1 (p.2+1)).re = ((p.1:ℝ)+1)/2^n := Or.inl (gcorner_re n p.1 (p.2+1))
        exact mem_YSet_of_re_endpoint hpS hzsq hre
      · rw [hv]
        have hzsq : gcorner n (p.1+1) (p.2+1) ∈ dSq n p :=
          dSq_corner (Or.inr (gcorner_re_succ n p.1 (p.2+1)))
            (Or.inr (gcorner_im_succ n p.1 p.2))
        have hre : (gcorner n (p.1+1) (p.2+1)).re = (p.1:ℝ)/2^n ∨
            (gcorner n (p.1+1) (p.2+1)).re = ((p.1:ℝ)+1)/2^n :=
          Or.inr (gcorner_re_succ n p.1 (p.2+1))
        exact mem_YSet_of_re_endpoint hpS hzsq hre
    · obtain ⟨e, he, hzseg⟩ := Set.mem_iUnion₂.mp hzE
      rcases Finset.mem_union.mp he with hv | hh
      · rcases mem_gVEdges.mp hv with ⟨p, hpS, rfl⟩ | ⟨p, hpS, rfl⟩
        · rw [mem_vSeg] at hzseg
          obtain ⟨hre, h1, h2⟩ := hzseg
          have hre' : z.re = (p.1:ℝ)/2^n ∨ z.re = ((p.1:ℝ)+1)/2^n := Or.inl hre
          exact mem_YSet_of_re_endpoint hpS (dSq_of_re_endpoint hre' h1 h2) hre'
        · rw [mem_vSeg] at hzseg
          obtain ⟨hre, h1, h2⟩ := hzseg
          have hre' : z.re = (p.1:ℝ)/2^n ∨ z.re = ((p.1:ℝ)+1)/2^n :=
            Or.inr (by rw [hre]; push_cast; ring)
          exact mem_YSet_of_re_endpoint hpS (dSq_of_re_endpoint hre' h1 h2) hre'
      · rcases mem_gHEdges.mp hh with ⟨p, hpS, hbelow, rfl⟩
        rw [mem_hSeg] at hzseg
        obtain ⟨him, h1, h2⟩ := hzseg
        exact mem_YSet_of_bottom_edge hpS (dSq_of_im_endpoint him h1 h2) hbelow him

/-! ## Transferring a CW structure to a closed subspace -/

section Transfer

variable {X : Type*} [TopologicalSpace X] {C K : Set X}

theorem cwTrans_closedCell_subset (hC : Topology.CWComplex (X := X) C) (n : ℕ) (i : hC.cell n) :
    hC.map n i '' Metric.closedBall (0 : Fin n → ℝ) 1 ⊆ C := by
  intro x hx
  rw [← hC.union']
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨i, hx⟩⟩

def cwTransFun (hC : Topology.CWComplex (X := X) C) (hCK : C ⊆ K) (dflt : ↥K)
    (n : ℕ) (i : hC.cell n) (x : Fin n → ℝ) : ↥K := by
  classical
  exact if hx : x ∈ Metric.closedBall (0 : Fin n → ℝ) 1
    then ⟨hC.map n i x, hCK (cwTrans_closedCell_subset hC n i ⟨x, hx, rfl⟩)⟩
    else dflt

lemma cwTransFun_apply (hC : Topology.CWComplex (X := X) C) (hCK : C ⊆ K) (dflt : ↥K)
    (n : ℕ) (i : hC.cell n) {x : Fin n → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin n → ℝ) 1) :
    ((cwTransFun hC hCK dflt n i x : ↥K) : X) = hC.map n i x := by
  rw [cwTransFun, dif_pos hx]

lemma ContinuousOn.subtype_mk_of_eqOn {α : Type*} [TopologicalSpace α] {f : α → X} {s : Set α}
    {p : X → Prop} {g : α → Subtype p} (hf : ContinuousOn f s)
    (hg : ∀ x ∈ s, ((g x : X) = f x)) : ContinuousOn g s := by
  rw [continuousOn_iff_continuous_domRestrict] at hf ⊢
  have hp : ∀ y : ↥s, p ((s.domRestrict f) y) := fun y =>
    show p (f y.1) from (hg y.1 y.2) ▸ (g y.1).2
  refine (Continuous.subtype_mk hf hp).congr (fun y => ?_)
  exact Subtype.ext (hg y.1 y.2).symm

lemma continuousOn_cwTransFun (hC : Topology.CWComplex (X := X) C) (hCK : C ⊆ K) (dflt : ↥K)
    (n : ℕ) (i : hC.cell n) :
    ContinuousOn (cwTransFun hC hCK dflt n i) (Metric.closedBall (0 : Fin n → ℝ) 1) := by
  classical
  refine ContinuousOn.subtype_mk_of_eqOn (p := fun z => z ∈ K) (hC.continuousOn n i) ?_
  intro x hx
  exact cwTransFun_apply hC hCK dflt n i hx

def cwTransMap (hC : Topology.CWComplex (X := X) C) (hCK : C ⊆ K) (dflt : ↥K)
    (n : ℕ) (i : hC.cell n) : PartialEquiv (Fin n → ℝ) ↥K where
  toFun := cwTransFun hC hCK dflt n i
  invFun y := (hC.map n i).symm (y : X)
  source := Metric.ball 0 1
  target := {y : ↥K | (y : X) ∈ (hC.map n i).target}
  map_source' := by
    intro x hx
    have hx' : x ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := Metric.ball_subset_closedBall hx
    rw [cwTransFun, dif_pos hx']
    exact (hC.map n i).map_source (by rw [hC.source_eq n i]; exact hx)
  map_target' := by
    intro y hy
    simpa only [hC.source_eq n i] using (hC.map n i).map_target hy
  left_inv' := by
    intro x hx
    have hx' : x ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := Metric.ball_subset_closedBall hx
    rw [cwTransFun, dif_pos hx']
    exact (hC.map n i).left_inv (by rw [hC.source_eq n i]; exact hx)
  right_inv' := by
    intro y hy
    have hyb : (hC.map n i).symm (y : X) ∈ Metric.ball (0 : Fin n → ℝ) 1 := by
      rw [← hC.source_eq n i]; exact (hC.map n i).map_target hy
    have hyc : (hC.map n i).symm (y : X) ∈ Metric.closedBall (0 : Fin n → ℝ) 1 :=
      Metric.ball_subset_closedBall hyb
    rw [cwTransFun, dif_pos hyc]
    exact Subtype.ext ((hC.map n i).right_inv hy)

lemma cwTransFun_image_ball (hC : Topology.CWComplex (X := X) C) (hCK : C ⊆ K) (dflt : ↥K)
    (n : ℕ) (i : hC.cell n) :
    (fun x => cwTransFun hC hCK dflt n i x) '' Metric.ball (0 : Fin n → ℝ) 1 =
      {y : ↥K | (y : X) ∈ hC.map n i '' Metric.ball (0 : Fin n → ℝ) 1} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (cwTransFun_apply hC hCK dflt n i (Metric.ball_subset_closedBall hx)).symm⟩
  · rintro ⟨x, hx, heq⟩
    refine ⟨x, hx, ?_⟩
    refine Subtype.ext ?_
    rw [cwTransFun_apply hC hCK dflt n i (Metric.ball_subset_closedBall hx)]
    exact heq

lemma cwTransFun_image_closedBall (hC : Topology.CWComplex (X := X) C) (hCK : C ⊆ K)
    (dflt : ↥K) (n : ℕ) (i : hC.cell n) :
    (fun x => cwTransFun hC hCK dflt n i x) '' Metric.closedBall (0 : Fin n → ℝ) 1 =
      {y : ↥K | (y : X) ∈ hC.map n i '' Metric.closedBall (0 : Fin n → ℝ) 1} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (cwTransFun_apply hC hCK dflt n i hx).symm⟩
  · rintro ⟨x, hx, heq⟩
    refine ⟨x, hx, ?_⟩
    refine Subtype.ext ?_
    rw [cwTransFun_apply hC hCK dflt n i hx]
    exact heq

lemma cwTransMap_image_ball (hC : Topology.CWComplex (X := X) C) (hCK : C ⊆ K) (dflt : ↥K)
    (n : ℕ) (i : hC.cell n) :
    ((cwTransMap hC hCK dflt n i : PartialEquiv (Fin n → ℝ) ↥K) : (Fin n → ℝ) → ↥K)
        '' Metric.ball (0 : Fin n → ℝ) 1
      = {y : ↥K | (y : X) ∈ hC.map n i '' Metric.ball (0 : Fin n → ℝ) 1} :=
  cwTransFun_image_ball hC hCK dflt n i

lemma cwTransMap_image_closedBall (hC : Topology.CWComplex (X := X) C) (hCK : C ⊆ K)
    (dflt : ↥K) (n : ℕ) (i : hC.cell n) :
    ((cwTransMap hC hCK dflt n i : PartialEquiv (Fin n → ℝ) ↥K) : (Fin n → ℝ) → ↥K)
        '' Metric.closedBall (0 : Fin n → ℝ) 1
      = {y : ↥K | (y : X) ∈ hC.map n i '' Metric.closedBall (0 : Fin n → ℝ) 1} :=
  cwTransFun_image_closedBall hC hCK dflt n i

lemma cwTransMap_apply (hC : Topology.CWComplex (X := X) C) (hCK : C ⊆ K) (dflt : ↥K)
    (n : ℕ) (i : hC.cell n) {x : Fin n → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin n → ℝ) 1) :
    ((((cwTransMap hC hCK dflt n i : PartialEquiv (Fin n → ℝ) ↥K)
        : (Fin n → ℝ) → ↥K) x : ↥K) : X) = hC.map n i x :=
  cwTransFun_apply hC hCK dflt n i hx

lemma continuousOn_symm_cwTransMap (hC : Topology.CWComplex (X := X) C) (hCK : C ⊆ K)
    (dflt : ↥K) (n : ℕ) (i : hC.cell n) :
    ContinuousOn (cwTransMap hC hCK dflt n i).symm (cwTransMap hC hCK dflt n i).target := by
  have h1 : ContinuousOn (fun y : ↥K => (hC.map n i).symm (y : X))
      {y : ↥K | (y : X) ∈ (hC.map n i).target} :=
    ContinuousOn.comp (hC.continuousOn_symm n i) continuous_subtype_val.continuousOn
      (fun y hy => hy)
  exact h1

lemma cwTransMap_disjoint (hC : Topology.CWComplex (X := X) C) (hCK : C ⊆ K) (dflt : ↥K)
    {a b : Σ n, hC.cell n} (hab : a ≠ b) :
    Disjoint (cwTransMap hC hCK dflt a.1 a.2 '' Metric.ball (0 : Fin a.1 → ℝ) 1)
      (cwTransMap hC hCK dflt b.1 b.2 '' Metric.ball (0 : Fin b.1 → ℝ) 1) := by
  have hd := hC.pairwiseDisjoint' (Set.mem_univ a) (Set.mem_univ b) hab
  rw [Function.onFun_apply] at hd
  rw [Set.disjoint_left] at hd ⊢
  intro y hy1 hy2
  rw [cwTransMap_image_ball] at hy1 hy2
  exact hd hy1 hy2


set_option warn.classDefReducibility false in
noncomputable def cwTransComplex (hC : Topology.CWComplex (X := X) C) (hK : IsClosed K)
    (hCK : C ⊆ K) (dflt : ↥K) : Topology.CWComplex (X := ↥K) {z : ↥K | (z : X) ∈ C} where
  cell := hC.cell
  map := fun n i => cwTransMap hC hCK dflt n i
  source_eq := fun n i => rfl
  continuousOn := fun n i => continuousOn_cwTransFun hC hCK dflt n i
  continuousOn_symm := fun n i => continuousOn_symm_cwTransMap hC hCK dflt n i
  pairwiseDisjoint' := fun a _ b _ hab => cwTransMap_disjoint hC hCK dflt hab
  mapsTo' := fun n i => by
    obtain ⟨J, hJ⟩ := hC.mapsTo' n i
    refine ⟨J, fun x hx => ?_⟩
    have hxc : x ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := Metric.sphere_subset_closedBall hx
    have hxJ : hC.map n i x ∈ ⋃ (m < n) (j ∈ J m),
        hC.map m j '' Metric.closedBall (0 : Fin m → ℝ) 1 := hJ hx
    simp only [Set.mem_iUnion] at hxJ ⊢
    obtain ⟨m, hmn, j, hj, x', hx', heq⟩ := hxJ
    refine ⟨m, hmn, j, hj, x', hx', Subtype.ext ?_⟩
    exact (cwTransMap_apply hC hCK dflt m j hx').trans
      (heq.trans (cwTransMap_apply hC hCK dflt n i hxc).symm)
  closed' := fun A hA hcl => by
    have hsub : (Subtype.val '' A) ⊆ C := by
      rintro x ⟨a, ha, rfl⟩
      exact hA ha
    have hcl' : ∀ n (j : hC.cell n),
        IsClosed (Subtype.val '' A ∩ hC.map n j '' Metric.closedBall (0 : Fin n → ℝ) 1) := by
      intro n j
      have h1 := hcl n j
      have hset : Subtype.val ''
            (A ∩ ((cwTransMap hC hCK dflt n j : PartialEquiv (Fin n → ℝ) ↥K)
              : (Fin n → ℝ) → ↥K) '' Metric.closedBall (0 : Fin n → ℝ) 1)
          = Subtype.val '' A ∩ hC.map n j '' Metric.closedBall (0 : Fin n → ℝ) 1 := by
        ext x
        constructor
        · rintro ⟨a, ⟨haA, haE⟩, rfl⟩
          rw [cwTransMap_image_closedBall] at haE
          exact ⟨⟨a, haA, rfl⟩, haE⟩
        · rintro ⟨⟨a, haA, rfl⟩, hxE⟩
          refine ⟨a, ⟨haA, ?_⟩, rfl⟩
          rw [cwTransMap_image_closedBall]
          exact hxE
      rw [← hset]
      exact hK.isClosedMap_subtype_val _ h1
    have h3 : IsClosed (Subtype.val '' A) := hC.closed' _ hsub hcl'
    have h4 : IsClosed (Subtype.val ⁻¹' (Subtype.val '' A)) :=
      IsClosed.preimage (f := (Subtype.val : ↥K → X)) continuous_subtype_val h3
    rwa [Set.preimage_image_eq A Subtype.val_injective] at h4
  union' := by
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨n, j, hz⟩
      rw [cwTransMap_image_closedBall] at hz
      exact cwTrans_closedCell_subset hC n j hz
    · intro hz
      have hz' : (z : X) ∈ ⋃ (n : ℕ) (j : hC.cell n),
          hC.map n j '' Metric.closedBall (0 : Fin n → ℝ) 1 := by
        rw [hC.union']; exact hz
      simp only [Set.mem_iUnion] at hz'
      obtain ⟨n, j, x, hx, heq⟩ := hz'
      exact ⟨n, j, x, hx, Subtype.ext ((cwTransMap_apply hC hCK dflt n j hx).trans heq)⟩

lemma cwTransComplex_cell (hC : Topology.CWComplex (X := X) C) (hK : IsClosed K) (hCK : C ⊆ K)
    (dflt : ↥K) : (cwTransComplex hC hK hCK dflt).cell = hC.cell := rfl

set_option warn.classDefReducibility false in
noncomputable def cwTransComplexEmpty (hCemp : C = ∅) :
    Topology.CWComplex (X := ↥K) {z : ↥K | (z : X) ∈ C} where
  cell := fun _ => PEmpty
  map := fun n i => i.elim
  source_eq := fun n i => i.elim
  continuousOn := fun n i => i.elim
  continuousOn_symm := fun n i => i.elim
  pairwiseDisjoint' := fun a _ _ _ _ => a.2.elim
  mapsTo' := fun n i => i.elim
  closed' := fun A hA hcl => by
    have hAe : A = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      have hmem : (z : X) ∈ C := hA hz
      rw [hCemp] at hmem
      exact hmem
    rw [hAe]
    exact isClosed_empty
  union' := by
    ext z
    constructor
    · intro hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨n, j, -⟩ := hz
      exact j.elim
    · intro hz
      have hmem : (z : X) ∈ C := hz
      rw [hCemp] at hmem
      exact absurd hmem (Set.notMem_empty _)

theorem exists_cwComplex_subtype_of_subset {X : Type*} [TopologicalSpace X] {C K : Set X}
    (hCK : C ⊆ K) (hK : IsClosed K) (hC : Topology.CWComplex (X := X) C) :
    ∃ hC' : Topology.CWComplex (X := ↥K) {z : ↥K | (z : X) ∈ C},
      ∀ n : ℕ, IsEmpty (hC.cell n) → IsEmpty (hC'.cell n) := by
  classical
  by_cases hne : (K : Set X).Nonempty
  · obtain ⟨d0, hd0⟩ := hne
    refine ⟨cwTransComplex hC hK hCK ⟨d0, hd0⟩, ?_⟩
    intro n hn
    rw [cwTransComplex_cell]
    exact hn
  · have hKemp : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hCemp : C = ∅ := by
      rw [hKemp] at hCK
      exact Set.subset_empty_iff.mp hCK
    refine ⟨cwTransComplexEmpty hCemp, ?_⟩
    intro n _
    exact ⟨fun x => x.elim⟩


/-! ## Assembly -/

lemma YSet_empty (n : ℕ) (S : Finset (ℤ × ℤ)) : YSet n S ∅ = ⋃ p ∈ S, dSq n p := by
  ext z; simp [YSet]

lemma YSet_biUnion_mono {n : ℕ} {A B : Finset (ℤ × ℤ)} (h : A ⊆ B) :
    (⋃ p ∈ A, dRemoved n p) ⊆ (⋃ p ∈ B, dRemoved n p) := by
  intro z hz
  simp only [Set.mem_iUnion] at hz ⊢
  obtain ⟨p, hpA, hzp⟩ := hz
  exact ⟨p, h hpA, hzp⟩

lemma YSet_antitone (n : ℕ) (S : Finset (ℤ × ℤ)) {A B : Finset (ℤ × ℤ)} (h : A ⊆ B) :
    YSet n S B ⊆ YSet n S A := by
  rintro z ⟨hzK, hzB⟩
  exact ⟨hzK, fun hzA => hzB (YSet_biUnion_mono h hzA)⟩

end Transfer

end Commons.Topology.Plane

namespace Commons.Topology.Plane

/-- The unit-square fold gives a fold datum for every dyadic square. -/
theorem exists_dyadicFold (n : ℕ) : Nonempty (∀ q : ℤ × ℤ, DFold n q) := by
  obtain ⟨uφ, uH, hcontφ, hcontH, hHmem, hH0, hH1, hφmem, hφfix, hφout, hHfix, hHout⟩ :=
    Commons.Topology.Plane.exists_fold_unitSq
  exact ⟨fun q => DFold.ofUnit n q uφ uH hcontφ hcontH hHmem hH0 hH1 hφmem hφfix hφout
    hHfix hHout⟩

theorem exists_homotopyEquiv_subgraph_oneDimCW_of_dyadic_subcomplex
    (n : ℕ) (S : Finset (ℤ × ℤ)) :
    let K : Set ℂ := ⋃ p ∈ S,
      {z : ℂ | (p.1 : ℝ) / 2 ^ n ≤ z.re ∧ z.re ≤ ((p.1 : ℝ) + 1) / 2 ^ n ∧
               (p.2 : ℝ) / 2 ^ n ≤ z.im ∧ z.im ≤ ((p.2 : ℝ) + 1) / 2 ^ n}
    ∃ (G : Set K) (hC : @Topology.CWComplex K _ G),
      (∀ m : ℕ, 2 ≤ m → IsEmpty (@Topology.CWComplex.cell K _ G hC m)) ∧
      Nonempty (ContinuousMap.HomotopyEquiv K ↥G) := by
  obtain ⟨fold⟩ := exists_dyadicFold n
  change ∃ (G : Set ↥(⋃ p ∈ S, dSq n p)) (hC : @Topology.CWComplex ↥(⋃ p ∈ S, dSq n p) _ G),
      (∀ m : ℕ, 2 ≤ m → IsEmpty (@Topology.CWComplex.cell ↥(⋃ p ∈ S, dSq n p) _ G hC m)) ∧
      Nonempty (ContinuousMap.HomotopyEquiv ↥(⋃ p ∈ S, dSq n p) ↥G)
  rw [← YSet_empty n S]
  obtain ⟨e⟩ := yset_chain n S fold ∅ (Finset.empty_subset S) (by intro q hq; simp at hq)
  obtain ⟨hCseg, hcellseg⟩ := exists_cwComplex_of_finset_segments (gVerts n S) (gEdges n S)
    (fun _ he => gEdges_endpoints_mem_gVerts he) (fun _ he => gEdges_ne he)
    (fun _ he _ he' hne' => gEdges_disjoint_segments he he' hne')
  have hKclosed : IsClosed (YSet n S ∅) := by
    rw [YSet_empty]
    exact isClosed_biUnion_finset (fun p _ => isClosed_dSq n p)
  have hsub : ((gVerts n S : Set ℂ) ∪ ⋃ e ∈ gEdges n S, segment ℝ e.1 e.2) ⊆ YSet n S ∅ := by
    rw [← YSet_eq_segments n S]
    exact YSet_antitone n S (Finset.empty_subset S)
  obtain ⟨hC', hcell'⟩ := exists_cwComplex_subtype_of_subset hsub hKclosed hCseg
  refine ⟨{z : ↥(YSet n S ∅) |
    (z:ℂ) ∈ (gVerts n S : Set ℂ) ∪ ⋃ e ∈ gEdges n S, segment ℝ e.1 e.2}, hC', ?_, ?_⟩
  · intro m hm
    exact hcell' m (hcellseg m hm)
  · have hhomeo : ↥(YSet n S S) ≃ₜ
        ↥{z : ↥(YSet n S ∅) |
          (z:ℂ) ∈ (gVerts n S : Set ℂ) ∪ ⋃ e ∈ gEdges n S, segment ℝ e.1 e.2} :=
      { toFun := fun w => ⟨⟨(w:ℂ), YSet_antitone n S (Finset.empty_subset S) w.2⟩, by
          rw [← YSet_eq_segments n S]; exact w.2⟩
        invFun := fun w => ⟨(w:ℂ), by
          rw [YSet_eq_segments n S]
          exact w.2⟩
        left_inv := fun w => Subtype.ext rfl
        right_inv := fun w => Subtype.ext rfl
        continuous_toFun := by
          have h1 : Continuous (fun w : ↥(YSet n S S) =>
              (⟨(w:ℂ), YSet_antitone n S (Finset.empty_subset S) w.2⟩ : ↥(YSet n S ∅))) :=
            Continuous.subtype_mk continuous_subtype_val _
          exact Continuous.subtype_mk h1 _
        continuous_invFun := Continuous.subtype_mk
          (continuous_subtype_val.comp continuous_subtype_val) (fun w => by
            rw [YSet_eq_segments n S]
            exact w.2) }
    exact ⟨e.trans hhomeo.toHomotopyEquiv⟩


end Commons.Topology.Plane
