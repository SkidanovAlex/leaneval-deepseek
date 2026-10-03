import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.Assembly

namespace Work.FIArea4.L14

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Auxiliary arithmetic facts

`oddPart d = d / 2 ^ (d.factorization 2)` is Mathlib's `Nat.ordCompl 2 d`; the lemmas below
record that it is multiplicative, and that multiplying by a square does not change the
predicate "is not a perfect square" (the predicate carried by the filters of the two sums). -/

lemma oddPart_mul (a b : ℕ) :
    Work.FIPlan.oddPart (a * b) = Work.FIPlan.oddPart a * Work.FIPlan.oddPart b := by
  rw [Work.FIPlan.oddPart, Work.FIPlan.oddPart, Work.FIPlan.oddPart]
  exact Nat.ordCompl_mul a b 2

lemma oddPart_one_le {b : ℕ} (hb : 1 ≤ b) : 1 ≤ Work.FIPlan.oddPart b :=
  Work.FIArea4.oddPart_pos (by omega)

/-- `√(m²X)² = m²X ↔ √X² = X`: multiplying by a nonzero square does not change the property
of being a perfect square. -/
lemma sqrt_sq_mul_sq_iff (m X : ℕ) (hm : 1 ≤ m) :
    (Nat.sqrt (m ^ 2 * X)) ^ 2 = m ^ 2 * X ↔ (Nat.sqrt X) ^ 2 = X := by
  rw [← Nat.exists_mul_self', ← Nat.exists_mul_self']
  constructor
  · rintro ⟨k, hk⟩
    have hdvd : m ∣ k := by
      refine (Nat.pow_dvd_pow_iff (n := 2) (by norm_num : (2 : ℕ) ≠ 0)).mp ?_
      exact ⟨X, hk⟩
    obtain ⟨q, rfl⟩ := hdvd
    refine ⟨q, ?_⟩
    have hk' : m ^ 2 * q ^ 2 = m ^ 2 * X := by rw [mul_pow] at hk; exact hk
    exact mul_left_cancel₀ (by positivity : m ^ 2 ≠ 0) hk'
  · rintro ⟨k, hk⟩
    exact ⟨m * k, by rw [mul_pow, hk]⟩

/-- The "not a perfect square" predicate of the two sums is invariant under scaling both
arguments by the same factor `m ≥ 1`. -/
lemma nc_scale (m a b : ℕ) (hm : 1 ≤ m) :
    (Nat.sqrt (Work.FIPlan.oddPart (m * a) * Work.FIPlan.oddPart (m * b)) ^ 2
        ≠ Work.FIPlan.oddPart (m * a) * Work.FIPlan.oddPart (m * b))
      ↔ (Nat.sqrt (Work.FIPlan.oddPart a * Work.FIPlan.oddPart b) ^ 2
        ≠ Work.FIPlan.oddPart a * Work.FIPlan.oddPart b) := by
  have hm' : 1 ≤ Work.FIPlan.oddPart m := oddPart_one_le hm
  have hmul : Work.FIPlan.oddPart (m * a) * Work.FIPlan.oddPart (m * b)
      = (Work.FIPlan.oddPart m) ^ 2 * (Work.FIPlan.oddPart a * Work.FIPlan.oddPart b) := by
    rw [oddPart_mul, oddPart_mul]; ring
  rw [hmul]
  exact not_congr (sqrt_sq_mul_sq_iff (Work.FIPlan.oddPart m)
    (Work.FIPlan.oddPart a * Work.FIPlan.oddPart b) hm')

lemma gcd_mul_div_left (a b : ℕ) : Nat.gcd a b * (a / Nat.gcd a b) = a :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)

lemma gcd_mul_div_right (a b : ℕ) : Nat.gcd a b * (b / Nat.gcd a b) = b := by
  rw [Nat.gcd_comm]
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_left b a)

/-- `[a,b] = (a,b)·(a/(a,b))·(b/(a,b))`. -/
lemma lcm_eq_gcd_mul_div (a b : ℕ) :
    Nat.lcm a b = Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rw [Nat.lcm_zero_left]; simp
  · have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
    have h2 : Nat.gcd a b * Nat.lcm a b
        = Nat.gcd a b * (Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b)) := by
      calc Nat.gcd a b * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
        _ = (Nat.gcd a b * (a / Nat.gcd a b)) * (Nat.gcd a b * (b / Nat.gcd a b)) := by
              rw [gcd_mul_div_left, gcd_mul_div_right]
        _ = Nat.gcd a b * (Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b)) := by ring
    exact Nat.mul_left_cancel hg h2

/-! ## The summands of the two sums -/

/-- The summand of the left-hand sum, as a function of the pair `(d₁,d₂)`. -/
def fv (R' : ℕ) (x : ℕ × ℕ) : ℝ :=
  (((Nat.lcm x.1 x.2 : ℕ) : ℝ)⁻¹) *
    (∑ r ∈ Finset.Icc 1 R',
      (jacobiSym (r : ℤ) (Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2) : ℝ)) ^ 2

/-- The summand of the right-hand sum, as a function of the triple `(e,b₁,b₂)`. -/
def gv (R' : ℕ) (z : ℕ × (ℕ × ℕ)) : ℝ :=
  (((z.1 * z.2.1 * z.2.2 : ℕ) : ℝ)⁻¹) *
    (∑ r ∈ Finset.Icc 1 R',
      (jacobiSym (r : ℤ) (Work.FIPlan.oddPart (z.1 * z.2.1)
        * Work.FIPlan.oddPart (z.1 * z.2.2)) : ℝ)) ^ 2

/-- The reindexing map `(d₁,d₂) ↦ ((d₁,d₂), d₁/(d₁,d₂), d₂/(d₁,d₂))`. -/
def phi (x : ℕ × ℕ) : ℕ × (ℕ × ℕ) :=
  (Nat.gcd x.1 x.2, (x.1 / Nat.gcd x.1 x.2, x.2 / Nat.gcd x.1 x.2))

lemma gv_nonneg (R' : ℕ) (z : ℕ × (ℕ × ℕ)) : 0 ≤ gv R' z :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (sq_nonneg _)

/-- On the image of `phi`, the right-hand summand equals the left-hand one. -/
lemma gv_phi_eq_fv (R' : ℕ) (x : ℕ × ℕ) : gv R' (phi x) = fv R' x := by
  obtain ⟨a, b⟩ := x
  have h1 : Nat.gcd a b * (a / Nat.gcd a b) = a := gcd_mul_div_left a b
  have h2 : Nat.gcd a b * (b / Nat.gcd a b) = b := gcd_mul_div_right a b
  have hl : Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b) = Nat.lcm a b :=
    (lcm_eq_gcd_mul_div a b).symm
  simp only [fv, gv, phi]
  rw [hl, h1, h2]

/-- `phi` is injective. -/
lemma phi_injective : Function.Injective phi := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  have hg : Nat.gcd a1 a2 = Nat.gcd b1 b2 := congrArg (fun z => z.1) h
  have h1 : a1 / Nat.gcd a1 a2 = b1 / Nat.gcd b1 b2 := congrArg (fun z => z.2.1) h
  have h2 : a2 / Nat.gcd a1 a2 = b2 / Nat.gcd b1 b2 := congrArg (fun z => z.2.2) h
  have e1 : Nat.gcd a1 a2 * (a1 / Nat.gcd a1 a2) = a1 := gcd_mul_div_left a1 a2
  have e2 : Nat.gcd b1 b2 * (b1 / Nat.gcd b1 b2) = b1 := gcd_mul_div_left b1 b2
  have f1 : Nat.gcd a1 a2 * (a2 / Nat.gcd a1 a2) = a2 := gcd_mul_div_right a1 a2
  have f2 : Nat.gcd b1 b2 * (b2 / Nat.gcd b1 b2) = b2 := gcd_mul_div_right b1 b2
  simp only [Prod.mk.injEq]
  constructor
  · calc a1 = Nat.gcd a1 a2 * (a1 / Nat.gcd a1 a2) := e1.symm
      _ = Nat.gcd b1 b2 * (b1 / Nat.gcd b1 b2) := by rw [h1, hg]
      _ = b1 := e2
  · calc a2 = Nat.gcd a1 a2 * (a2 / Nat.gcd a1 a2) := f1.symm
      _ = Nat.gcd b1 b2 * (b2 / Nat.gcd b1 b2) := by rw [h2, hg]
      _ = b2 := f2

/-- A pair of the left index set is mapped by `phi` into the right index set: the gcd and the
two quotients are in `[1,D]`, and the quotient pair still satisfies the "not a perfect square"
condition (the predicate is invariant under scaling by the gcd). -/
lemma phi_mem {D : ℕ} {x : ℕ × ℕ}
    (hx1 : x.1 ∈ Finset.Icc 1 D) (hx2 : x.2 ∈ Finset.Icc 1 D)
    (hP : Nat.sqrt (Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2) ^ 2
        ≠ Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2) :
    phi x ∈ Finset.Icc 1 D ×ˢ
      ((Finset.Icc 1 D ×ˢ Finset.Icc 1 D).filter
        (fun y : ℕ × ℕ => Nat.sqrt (Work.FIPlan.oddPart y.1 * Work.FIPlan.oddPart y.2) ^ 2
          ≠ Work.FIPlan.oddPart y.1 * Work.FIPlan.oddPart y.2)) := by
  have hx1a : 1 ≤ x.1 := (Finset.mem_Icc.mp hx1).1
  have hx1D : x.1 ≤ D := (Finset.mem_Icc.mp hx1).2
  have hx2a : 1 ≤ x.2 := (Finset.mem_Icc.mp hx2).1
  have hx2D : x.2 ≤ D := (Finset.mem_Icc.mp hx2).2
  have hx1pos : 0 < x.1 := by omega
  have hx2pos : 0 < x.2 := by omega
  have hg1 : 1 ≤ Nat.gcd x.1 x.2 := by
    have := Nat.gcd_pos_of_pos_left x.2 hx1pos
    omega
  have hgD : Nat.gcd x.1 x.2 ≤ D := le_trans (Nat.gcd_le_left x.2 hx1pos) hx1D
  have hb1a : 1 ≤ x.1 / Nat.gcd x.1 x.2 := by
    rw [Nat.one_le_div_iff (by omega : 0 < Nat.gcd x.1 x.2)]
    exact Nat.gcd_le_left x.2 hx1pos
  have hb2a : 1 ≤ x.2 / Nat.gcd x.1 x.2 := by
    rw [Nat.one_le_div_iff (by omega : 0 < Nat.gcd x.1 x.2), Nat.gcd_comm]
    exact Nat.gcd_le_left x.1 hx2pos
  have hb1D : x.1 / Nat.gcd x.1 x.2 ≤ D := le_trans (Nat.div_le_self x.1 _) hx1D
  have hb2D : x.2 / Nat.gcd x.1 x.2 ≤ D := le_trans (Nat.div_le_self x.2 _) hx2D
  rw [Finset.mem_product]
  refine ⟨Finset.mem_Icc.mpr ⟨hg1, hgD⟩, ?_⟩
  rw [Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨Finset.mem_Icc.mpr ⟨hb1a, hb1D⟩, Finset.mem_Icc.mpr ⟨hb2a, hb2D⟩⟩, ?_⟩
  have hscale : (Nat.sqrt (Work.FIPlan.oddPart (Nat.gcd x.1 x.2 * (x.1 / Nat.gcd x.1 x.2))
          * Work.FIPlan.oddPart (Nat.gcd x.1 x.2 * (x.2 / Nat.gcd x.1 x.2))) ^ 2
        ≠ Work.FIPlan.oddPart (Nat.gcd x.1 x.2 * (x.1 / Nat.gcd x.1 x.2))
          * Work.FIPlan.oddPart (Nat.gcd x.1 x.2 * (x.2 / Nat.gcd x.1 x.2))) := by
    rw [gcd_mul_div_left, gcd_mul_div_right]
    exact hP
  simp only [phi]
  exact (nc_scale (Nat.gcd x.1 x.2) (x.1 / Nat.gcd x.1 x.2) (x.2 / Nat.gcd x.1 x.2) hg1).mp hscale

/-- Reindexing the double sum: the sum over the pairs `(b₁,b₂)` of the two filtered sets equals
the sum over the filtered product. -/
lemma prod_filter_sum (s : Finset ℕ) (p : ℕ → ℕ → Prop) (g : ℕ × ℕ → ℝ) :
    (∑ x ∈ (s ×ˢ s).filter (fun x => p x.1 x.2), g x)
      = ∑ b1 ∈ s, ∑ b2 ∈ s.filter (fun b2 => p b1 b2), g (b1, b2) := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_product (s) (s) (fun x => if p x.1 x.2 then g x else 0)]

/-! ## The reindexing theorem -/

/-- Reindexing the double sum `T'` by the gcd: for `(d₁,d₂)` with `e = gcd(d₁,d₂)`,
`b₁ = d₁/e`, `b₂ = d₂/e` one has `lcm(d₁,d₂) = e·b₁·b₂`, `d₁ = e·b₁`, `d₂ = e·b₂`, and
`d₁'d₂' ≠ □ ↔ b₁'b₂' ≠ □` (as `d₁'d₂' = (e')² b₁'b₂'`).  Summing over the larger set of triples
`(e,b₁,b₂) ∈ [1,D]³` with `b₁'b₂' ≠ □` gives the upper bound. -/
theorem T_to_U :
    ∀ (D R' : ℕ), 1 ≤ D →
      (∑ d1 ∈ Finset.Icc 1 D,
        ∑ d2 ∈ (Finset.Icc 1 D).filter
            (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                        ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹) *
            (∑ r ∈ Finset.Icc 1 R', (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℝ))^2)
      ≤ (∑ e ∈ Finset.Icc 1 D,
          ∑ b1 ∈ Finset.Icc 1 D,
          ∑ b2 ∈ (Finset.Icc 1 D).filter
              (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2
                          ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
            (((e * b1 * b2 : ℕ) : ℝ)⁻¹) *
              (∑ r ∈ Finset.Icc 1 R', (jacobiSym (r : ℤ) (Work.FIPlan.oddPart (e * b1) * Work.FIPlan.oddPart (e * b2)) : ℝ))^2)
    := by
  intro D R' hD
  have hL : (∑ d1 ∈ Finset.Icc 1 D,
        ∑ d2 ∈ (Finset.Icc 1 D).filter
            (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                        ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹) *
            (∑ r ∈ Finset.Icc 1 R', (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℝ))^2)
      = ∑ x ∈ (Finset.Icc 1 D ×ˢ Finset.Icc 1 D).filter
          (fun x : ℕ × ℕ => Nat.sqrt (Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2) ^ 2
                        ≠ Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2), fv R' x := by
    have h0 : (∑ d1 ∈ Finset.Icc 1 D,
        ∑ d2 ∈ (Finset.Icc 1 D).filter
            (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                        ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹) *
            (∑ r ∈ Finset.Icc 1 R', (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℝ))^2)
        = ∑ d1 ∈ Finset.Icc 1 D,
            ∑ d2 ∈ (Finset.Icc 1 D).filter
              (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                          ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2), fv R' (d1, d2) := by
      refine Finset.sum_congr rfl (fun d1 _ => Finset.sum_congr rfl (fun d2 _ => ?_))
      rfl
    rw [h0]
    simp only [Finset.sum_filter]
    rw [← Finset.sum_product (Finset.Icc 1 D) (Finset.Icc 1 D)
      (fun x : ℕ × ℕ => if Nat.sqrt (Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2) ^ 2
                        ≠ Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2 then fv R' x else 0)]
  have hE : (∑ e ∈ Finset.Icc 1 D,
          ∑ b1 ∈ Finset.Icc 1 D,
          ∑ b2 ∈ (Finset.Icc 1 D).filter
              (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2
                          ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
            (((e * b1 * b2 : ℕ) : ℝ)⁻¹) *
              (∑ r ∈ Finset.Icc 1 R', (jacobiSym (r : ℤ) (Work.FIPlan.oddPart (e * b1) * Work.FIPlan.oddPart (e * b2)) : ℝ))^2)
      = ∑ e ∈ Finset.Icc 1 D,
          ∑ b1 ∈ Finset.Icc 1 D,
          ∑ b2 ∈ (Finset.Icc 1 D).filter
              (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2
                          ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2), gv R' (e, b1, b2) := by
    refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun b1 _ =>
      Finset.sum_congr rfl (fun b2 _ => ?_)))
    rfl
  have hstep : ∀ e ∈ Finset.Icc 1 D,
      (∑ b1 ∈ Finset.Icc 1 D,
        ∑ b2 ∈ (Finset.Icc 1 D).filter
            (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2
                        ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
          gv R' (e, b1, b2))
      = ∑ x ∈ (Finset.Icc 1 D ×ˢ Finset.Icc 1 D).filter
          (fun x : ℕ × ℕ => Nat.sqrt (Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2) ^ 2
                        ≠ Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2), gv R' (e, x) := by
    intro e _
    simp only [Finset.sum_filter]
    rw [← Finset.sum_product (Finset.Icc 1 D) (Finset.Icc 1 D)
      (fun x : ℕ × ℕ => if Nat.sqrt (Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2) ^ 2
                        ≠ Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2
                        then gv R' (e, x) else 0)]
  have hsub : ((Finset.Icc 1 D ×ˢ Finset.Icc 1 D).filter
        (fun x : ℕ × ℕ => Nat.sqrt (Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2) ^ 2
                      ≠ Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2)).image phi
      ⊆ Finset.Icc 1 D ×ˢ ((Finset.Icc 1 D ×ˢ Finset.Icc 1 D).filter
        (fun x : ℕ × ℕ => Nat.sqrt (Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2) ^ 2
                      ≠ Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2)) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hxA, rfl⟩ := hz
    rw [Finset.mem_filter, Finset.mem_product] at hxA
    exact phi_mem hxA.1.1 hxA.1.2 hxA.2
  have hinj : Set.InjOn phi ↑((Finset.Icc 1 D ×ˢ Finset.Icc 1 D).filter
        (fun x : ℕ × ℕ => Nat.sqrt (Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2) ^ 2
                      ≠ Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2)) :=
    fun x _ y _ h => phi_injective h
  calc (∑ d1 ∈ Finset.Icc 1 D,
        ∑ d2 ∈ (Finset.Icc 1 D).filter
            (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                        ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹) *
            (∑ r ∈ Finset.Icc 1 R', (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℝ))^2)
      = ∑ x ∈ (Finset.Icc 1 D ×ˢ Finset.Icc 1 D).filter
          (fun x : ℕ × ℕ => Nat.sqrt (Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2) ^ 2
                        ≠ Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2), fv R' x := hL
    _ = ∑ x ∈ (Finset.Icc 1 D ×ˢ Finset.Icc 1 D).filter
          (fun x : ℕ × ℕ => Nat.sqrt (Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2) ^ 2
                        ≠ Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2), gv R' (phi x) :=
          Finset.sum_congr rfl (fun x _ => (gv_phi_eq_fv R' x).symm)
    _ = ∑ z ∈ ((Finset.Icc 1 D ×ˢ Finset.Icc 1 D).filter
          (fun x : ℕ × ℕ => Nat.sqrt (Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2) ^ 2
                        ≠ Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2)).image phi, gv R' z :=
          (Finset.sum_image hinj).symm
    _ ≤ ∑ z ∈ Finset.Icc 1 D ×ˢ ((Finset.Icc 1 D ×ˢ Finset.Icc 1 D).filter
          (fun x : ℕ × ℕ => Nat.sqrt (Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2) ^ 2
                        ≠ Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2)), gv R' z :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => gv_nonneg R' z)
    _ = ∑ e ∈ Finset.Icc 1 D,
          ∑ b1 ∈ Finset.Icc 1 D,
          ∑ b2 ∈ (Finset.Icc 1 D).filter
              (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2
                          ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
            (((e * b1 * b2 : ℕ) : ℝ)⁻¹) *
              (∑ r ∈ Finset.Icc 1 R', (jacobiSym (r : ℤ) (Work.FIPlan.oddPart (e * b1) * Work.FIPlan.oddPart (e * b2)) : ℝ))^2 := by
          rw [hE, Finset.sum_congr rfl hstep,
            Finset.sum_product (Finset.Icc 1 D) ((Finset.Icc 1 D ×ˢ Finset.Icc 1 D).filter
                (fun x : ℕ × ℕ => Nat.sqrt (Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2) ^ 2
                      ≠ Work.FIPlan.oddPart x.1 * Work.FIPlan.oddPart x.2)) (gv R')]

end

end Work.FIArea4.L14
