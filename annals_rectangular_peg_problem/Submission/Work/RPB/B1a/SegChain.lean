/-
# Polygonal chains and their integrals (B1a, node N5 support)

This file sets up the elementary calculus of integrals of a function `f : ℂ → ℂ` along a polygonal
chain, represented as a `List (ℂ × ℂ)` of segments.  It is the shared vocabulary for the
in-house proof of `Work.RPB.B1a.hasPrimitives_of_isConnected_compl` (Cauchy's theorem for a bounded
domain with connected complement).

Everything here is elementary: linearity, concatenation, and the fundamental theorem of calculus
along a segment (which gives the vanishing of the integral along a closed chain for any function
admitting a primitive on a neighbourhood of the chain).
-/
import Mathlib

namespace Work.RPB.B1a

open Complex Set MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

/-- Integral of `f : ℂ → ℂ` along the segment from `a` to `b`, parametrized as
`t ↦ a + t * (b - a)`, `t ∈ [0,1]`. -/
def segIntegral (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, f (a + (t : ℂ) * (b - a)) * (b - a)

/-- Integral of `f` along the polygonal chain represented by a list of segments. -/
def chainIntegral (f : ℂ → ℂ) (L : List (ℂ × ℂ)) : ℂ :=
  (L.map (fun s => segIntegral f s.1 s.2)).sum

/-- `IsChainFrom p q L` : the list of segments `L` is a polygonal chain running from `p` to `q`,
i.e. the end point of each segment is the start point of the next. -/
def IsChainFrom (p q : ℂ) : List (ℂ × ℂ) → Prop
  | [] => p = q
  | s :: L => s.1 = p ∧ IsChainFrom s.2 q L

/-- Every segment of the chain `L` lies in the open set `U`. -/
def ChainIn (U : Set ℂ) (L : List (ℂ × ℂ)) : Prop :=
  ∀ s ∈ L, s.1 ∈ U ∧ s.2 ∈ U ∧ segment ℝ s.1 s.2 ⊆ U

/-- The trace (union of the segments) of a polygonal chain. -/
def chainTrace (L : List (ℂ × ℂ)) : Set ℂ :=
  {z | ∃ s ∈ L, z ∈ segment ℝ s.1 s.2}

variable {f g F : ℂ → ℂ} {a b c : ℂ} {L L₁ L₂ : List (ℂ × ℂ)}

lemma mem_segment_self_left (a b : ℂ) : a ∈ segment ℝ a b :=
  left_mem_segment ℝ a b

lemma mem_segment_param {a b : ℂ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    a + (t : ℂ) * (b - a) ∈ segment ℝ a b := by
  rw [segment_eq_image']
  exact ⟨t, ht, by simp [Complex.real_smul]⟩

/-! ## Elementary properties of `chainIntegral` -/

@[simp] lemma chainIntegral_nil : chainIntegral f [] = 0 := rfl

@[simp] lemma chainIntegral_cons (a b : ℂ) (L : List (ℂ × ℂ)) :
    chainIntegral f ((a, b) :: L) = segIntegral f a b + chainIntegral f L := by
  simp [chainIntegral]

lemma chainIntegral_append (L₁ L₂ : List (ℂ × ℂ)) :
    chainIntegral f (L₁ ++ L₂) = chainIntegral f L₁ + chainIntegral f L₂ := by
  simp [chainIntegral, List.map_append, List.sum_append]

@[simp] lemma chainIntegral_singleton (a b : ℂ) :
    chainIntegral f [(a, b)] = segIntegral f a b := by
  simp [chainIntegral]

/-- The chain integral only depends on the values of `f` on the trace of the chain. -/
lemma chainIntegral_congr {f g : ℂ → ℂ} (L : List (ℂ × ℂ))
    (h : ∀ s ∈ L, ∀ z ∈ segment ℝ s.1 s.2, f z = g z) :
    chainIntegral f L = chainIntegral g L := by
  induction L with
  | nil => simp
  | cons s L ih =>
    obtain ⟨a, b⟩ := s
    have h1 : segIntegral f a b = segIntegral g a b := by
      simp only [segIntegral]
      refine intervalIntegral.integral_congr fun t ht => ?_
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
      rw [h (a, b) (by simp) _ (mem_segment_param ht')]
    rw [chainIntegral_cons, chainIntegral_cons, h1,
      ih fun s hs z hz => h s (by simp [hs]) z hz]

lemma segIntegral_const_mul (c : ℂ) (a b : ℂ) :
    segIntegral (fun z => c * f z) a b = c * segIntegral f a b := by
  simp only [segIntegral]
  rw [show (fun t : ℝ => c * f (a + (t : ℂ) * (b - a)) * (b - a))
        = fun t : ℝ => c * (f (a + (t : ℂ) * (b - a)) * (b - a)) from by
    funext t; ring,
    intervalIntegral.integral_const_mul]

lemma chainIntegral_const_mul (c : ℂ) (L : List (ℂ × ℂ)) :
    chainIntegral (fun z => c * f z) L = c * chainIntegral f L := by
  induction L with
  | nil => simp
  | cons s L ih =>
    obtain ⟨a, b⟩ := s
    rw [chainIntegral_cons, chainIntegral_cons, segIntegral_const_mul, ih, mul_add]

lemma chainIntegral_neg (L : List (ℂ × ℂ)) :
    chainIntegral (fun z => -f z) L = -chainIntegral f L := by
  simpa using chainIntegral_const_mul (f := f) (-1) L

@[simp] lemma segIntegral_self (f : ℂ → ℂ) (a : ℂ) : segIntegral f a a = 0 := by
  simp [segIntegral]

@[simp] lemma segIntegral_one (a b : ℂ) : segIntegral (fun _ : ℂ => 1) a b = b - a := by
  have hone : (fun t : ℝ => (1 : ℂ) * (b - a)) = fun _ : ℝ => (b - a) := by funext t; ring
  simp only [segIntegral, hone, intervalIntegral.integral_const]
  simp

/-! ## Continuity and linearity helpers -/

lemma chainTrace_mono {L L' : List (ℂ × ℂ)} (h : ∀ s ∈ L, s ∈ L') :
    chainTrace L ⊆ chainTrace L' :=
  fun _ ⟨s, hs, hz⟩ => ⟨s, h s hs, hz⟩

lemma chainTrace_tail_subset_cons (a : ℂ × ℂ) (L : List (ℂ × ℂ)) :
    chainTrace L ⊆ chainTrace (a :: L) :=
  chainTrace_mono fun _ hs => List.mem_cons_of_mem _ hs

lemma segment_subset_chainTrace {s : ℂ × ℂ} {L : List (ℂ × ℂ)} (hs : s ∈ L) :
    segment ℝ s.1 s.2 ⊆ chainTrace L :=
  fun _ hz => ⟨s, hs, hz⟩

lemma segment_subset_chainTrace_of_head (a b : ℂ) (L : List (ℂ × ℂ)) :
    segment ℝ a b ⊆ chainTrace ((a, b) :: L) :=
  segment_subset_chainTrace (L := (a, b) :: L) List.mem_cons_self

lemma mem_chainTrace_param {s : ℂ × ℂ} {L : List (ℂ × ℂ)} (hs : s ∈ L) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : s.1 + (t : ℂ) * (s.2 - s.1) ∈ chainTrace L :=
  ⟨s, hs, mem_segment_param ht⟩

/-- The integrand of `segIntegral f a b` is interval integrable as soon as `f` is continuous on the
segment. -/
lemma intervalIntegrable_segIntegral {f : ℂ → ℂ} {a b : ℂ}
    (h : ContinuousOn f (segment ℝ a b)) :
    IntervalIntegrable (fun t : ℝ => f (a + (t : ℂ) * (b - a)) * (b - a)) volume 0 1 := by
  have hcont : ContinuousOn (fun t : ℝ => f (a + (t : ℂ) * (b - a))) (uIcc (0 : ℝ) 1) := by
    refine h.comp ?_ ?_
    · fun_prop
    · intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      exact mem_segment_param ht
  exact (hcont.mul continuousOn_const).intervalIntegrable

/-- Additivity of the chain integral in the integrand (under continuity hypotheses). -/
lemma chainIntegral_sub {f g : ℂ → ℂ} (L : List (ℂ × ℂ))
    (hf : ContinuousOn f (chainTrace L)) (hg : ContinuousOn g (chainTrace L)) :
    chainIntegral (fun z => f z - g z) L = chainIntegral f L - chainIntegral g L := by
  induction L with
  | nil => simp
  | cons s L ih =>
    obtain ⟨a, b⟩ := s
    have hsub : segIntegral (fun z => f z - g z) a b = segIntegral f a b - segIntegral g a b := by
      simp only [segIntegral]
      have h1 : (fun t : ℝ => (f (a + (t : ℂ) * (b - a)) - g (a + (t : ℂ) * (b - a))) * (b - a))
          = fun t : ℝ =>
              f (a + (t : ℂ) * (b - a)) * (b - a) - g (a + (t : ℂ) * (b - a)) * (b - a) := by
        funext t; ring
      rw [h1, intervalIntegral.integral_sub]
      · exact intervalIntegrable_segIntegral (hf.mono (segment_subset_chainTrace_of_head a b L))
      · exact intervalIntegrable_segIntegral (hg.mono (segment_subset_chainTrace_of_head a b L))
    simp only [chainIntegral_cons]
    rw [hsub, ih (hf.mono (chainTrace_tail_subset_cons (a, b) L))
        (hg.mono (chainTrace_tail_subset_cons (a, b) L))]
    ring

/-- Additivity of the chain integral in the integrand (under continuity hypotheses). -/
lemma chainIntegral_add {f g : ℂ → ℂ} (L : List (ℂ × ℂ))
    (hf : ContinuousOn f (chainTrace L)) (hg : ContinuousOn g (chainTrace L)) :
    chainIntegral (fun z => f z + g z) L = chainIntegral f L + chainIntegral g L := by
  induction L with
  | nil => simp
  | cons s L ih =>
    obtain ⟨a, b⟩ := s
    have hsub : segIntegral (fun z => f z + g z) a b = segIntegral f a b + segIntegral g a b := by
      simp only [segIntegral]
      have h1 : (fun t : ℝ => (f (a + (t : ℂ) * (b - a)) + g (a + (t : ℂ) * (b - a))) * (b - a))
          = fun t : ℝ =>
              f (a + (t : ℂ) * (b - a)) * (b - a) + g (a + (t : ℂ) * (b - a)) * (b - a) := by
        funext t; ring
      rw [h1, intervalIntegral.integral_add]
      · exact intervalIntegrable_segIntegral (hf.mono (segment_subset_chainTrace_of_head a b L))
      · exact intervalIntegrable_segIntegral (hg.mono (segment_subset_chainTrace_of_head a b L))
    simp only [chainIntegral_cons]
    rw [hsub, ih (hf.mono (chainTrace_tail_subset_cons (a, b) L))
        (hg.mono (chainTrace_tail_subset_cons (a, b) L))]
    ring

/-! ## The fundamental theorem of calculus along a segment -/

/-- **Fundamental theorem of calculus along a segment.** If `F` is a primitive of `f` along the
segment `[a,b]` and `f` is continuous there, then the segment integral of `f` is the increment
of `F`. -/
theorem segIntegral_eq_sub_of_hasDerivAt {f F : ℂ → ℂ} {a b : ℂ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F (f (a + (t : ℂ) * (b - a))) (a + (t : ℂ) * (b - a)))
    (hc : ContinuousOn f (segment ℝ a b)) :
    segIntegral f a b = F b - F a := by
  have hu : ∀ t : ℝ, HasDerivAt (fun ζ : ℂ => a + ζ * (b - a)) (b - a) (t : ℂ) := by
    intro t
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const (b - a)).const_add a
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => F (a + (y : ℂ) * (b - a)))
        (f (a + (t : ℂ) * (b - a)) * (b - a)) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
    exact ((h t ht').comp (t : ℂ) (hu t)).comp_ofReal
  have hint : IntervalIntegrable (fun t : ℝ => f (a + (t : ℂ) * (b - a)) * (b - a)) volume 0 1 :=
    intervalIntegrable_segIntegral hc
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [segIntegral]
  simpa using this

/-- **Telescoping of the chain integral.** The integral of `f` along a chain from `p` to `q`,
for a function `F` that is a primitive of `f` along every segment of the chain. -/
theorem chainIntegral_eq_sub_of_hasDerivAt {f F : ℂ → ℂ} {p q : ℂ} {L : List (ℂ × ℂ)}
    (hL : IsChainFrom p q L)
    (hF : ∀ s ∈ L, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt F (f (s.1 + (t : ℂ) * (s.2 - s.1))) (s.1 + (t : ℂ) * (s.2 - s.1)))
    (hc : ∀ s ∈ L, ContinuousOn f (segment ℝ s.1 s.2)) :
    chainIntegral f L = F q - F p := by
  induction L generalizing p with
  | nil =>
    simp only [chainIntegral_nil]
    rw [hL]
    ring
  | cons s L ih =>
    obtain ⟨a, b⟩ := s
    obtain ⟨h1, h2⟩ := hL
    rw [chainIntegral_cons, segIntegral_eq_sub_of_hasDerivAt (h := hF (a, b) (by simp))
      (hc := hc (a, b) (by simp)), ih h2 (fun s hs => hF s (by simp [hs]))
      (fun s hs => hc s (by simp [hs])), h1]
    ring

/-- The integral of `f` along a **closed** chain vanishes, provided `f` has a primitive along the
chain. -/
theorem chainIntegral_eq_zero_of_hasDerivAt {f F : ℂ → ℂ} {p : ℂ} {L : List (ℂ × ℂ)}
    (hL : IsChainFrom p p L)
    (hF : ∀ s ∈ L, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt F (f (s.1 + (t : ℂ) * (s.2 - s.1))) (s.1 + (t : ℂ) * (s.2 - s.1)))
    (hc : ∀ s ∈ L, ContinuousOn f (segment ℝ s.1 s.2)) :
    chainIntegral f L = 0 := by
  rw [chainIntegral_eq_sub_of_hasDerivAt hL hF hc, sub_self]

end

end Work.RPB.B1a
