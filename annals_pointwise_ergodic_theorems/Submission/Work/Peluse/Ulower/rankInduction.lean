import Mathlib
import Submission.Work.Peluse.Peel.boxSumPow_peel

/-!
# Rank induction for Peluse's Lemma 7.5: the base case (`rank 0`)

Start of the Peluse–Prendiville §6 route to `Work.Peluse.Ulower.lemma75_control`
(see `NOTES_lemma75_control.md`): instead of the plain Gowers–Cauchy–Schwarz step — which, as the
notes record, *erases* the phases and loses a factor `L` — one inducts on the **rank** of the
phase, each Cauchy–Schwarz step *differencing* the phase and so lowering its rank by one, with
plain Cauchy–Schwarz as the base case.

The base case, proved here, is the statement with **no phase at all**: the exact identity
`∑' x, G x = D⁻¹ ∑' x, ∑_{a ∈ arithIcc 1 D} G (x+a)` (the shift `x ↦ x+a` is a bijection of `ℤ`)
together with Cauchy–Schwarz on the support of the window sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- The cardinality of `arithIcc 1 D`. -/
lemma card_arithIcc_one (D : ℕ) : (arithIcc 1 D).card = D := by
  rw [arithIcc]
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp

/-- Membership in `arithIcc 1 D`. -/
lemma mem_arithIcc_one {D : ℕ} {a : ℤ} : a ∈ arithIcc 1 D ↔ 1 ≤ a ∧ a ≤ (D : ℤ) := by
  rw [arithIcc, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_Icc] at hj
    exact ⟨by simpa using (show (1 : ℤ) ≤ (j : ℤ) by exact_mod_cast hj.1),
      by simpa using (show (j : ℤ) ≤ (D : ℤ) by exact_mod_cast hj.2)⟩
  · intro ⟨h1, h2⟩
    refine ⟨a.toNat, ?_, ?_⟩
    · rw [Finset.mem_Icc]; omega
    · simp only [one_mul]; omega

/-- The cardinality of `symIcc N`. -/
lemma card_symIcc (N : ℕ) : (symIcc N).card = 2 * N + 1 := by
  rw [symIcc, Int.card_Icc]
  have h : ((N : ℤ) + 1 - (-(N : ℤ))) = 2 * (N : ℤ) + 1 := by ring
  rw [h]
  have h2 : (2 * (N : ℤ) + 1) = (((2 * N + 1 : ℕ)) : ℤ) := by push_cast; ring
  rw [h2, Int.toNat_natCast]

/-- The difference `Δ'_{a,b} f (u) = f (u + a) * conj (f (u + b))`, in the normalisation that
`Peel.boxSumPow_peel` produces. -/
def dif (a b : ℤ) (f : ℤ → ℂ) : ℤ → ℂ := fun u => f (u + a) * star (f (u + b))

/-- `dif a b f` is supported where `f` is, up to the shifts. -/
lemma supportIn_dif {f : ℤ → ℂ} {N : ℕ} (hf : SupportIn f N) (a b : ℤ) :
    SupportIn (dif a b f) (N + max a.natAbs b.natAbs) := by
  intro u hu
  have huZ : ((N + max a.natAbs b.natAbs : ℕ) : ℤ) < |u| := by
    have h1 : ((u.natAbs : ℕ) : ℤ) = |u| := Int.natCast_natAbs u
    rw [← h1]
    exact_mod_cast hu
  have huZ' : (N : ℤ) + ((max a.natAbs b.natAbs : ℕ) : ℤ) < |u| := by
    rw [Nat.cast_add] at huZ
    exact huZ
  have hmaxa : |a| ≤ ((max a.natAbs b.natAbs : ℕ) : ℤ) := by
    calc |a| = ((a.natAbs : ℕ) : ℤ) := (Int.natCast_natAbs a).symm
      _ ≤ ((max a.natAbs b.natAbs : ℕ) : ℤ) := by
          exact_mod_cast le_max_left a.natAbs b.natAbs
  have hua : (N : ℤ) < |u + a| := by
    have h := abs_add_le (u + a) (-a)
    have h2 : u + a + -a = u := by ring
    rw [h2, abs_neg] at h
    linarith
  have hfa : f (u + a) = 0 := by
    refine hf (u + a) ?_
    have h' : ((N : ℕ) : ℤ) < (((u + a).natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hua
    exact_mod_cast h'
  rw [dif, hfa, zero_mul]

/-- The difference of a finitely supported function is finitely supported. -/
lemma dif_finSuppZ {f : ℤ → ℂ} (hf : FinSuppZ f) (a b : ℤ) : FinSuppZ (dif a b f) := by
  obtain ⟨N, hN⟩ := hf
  exact ⟨N + max a.natAbs b.natAbs, supportIn_dif hN a b⟩

/-- **Peel of the box-norm power at a constant direction family.**  For `t ≥ 1`,

`‖f‖^{2^{t+1}}_{□^{t+1}_{Q,…,Q}(S)} = |Q|⁻² ∑_{a,b ∈ Q} ‖Δ'_{a,b} f‖^{2^t}_{□^t_{Q,…,Q}(S)}`. -/
theorem boxNormPow_succ_peel {t : ℕ} (ht : 1 ≤ t) (Q : Finset ℤ) (S : Finset ℤ)
    (f : ℤ → ℂ) (hfin : FinSuppZ f) :
    boxNormPow (t + 1) (fun _ : Fin (t + 1) => Q) S f
      = ((Q.card : ℝ))⁻¹ ^ 2 * ∑ a ∈ Q, ∑ b ∈ Q,
          boxNormPow t (fun _ : Fin t => Q) S (dif a b f) := by
  classical
  have hpeel := Peel.boxSumPow_peel (t := t) (Q := fun _ : Fin (t + 1) => Q) S f
  have hinner : ∀ h : ℤ, ∀ h' : ℤ,
      boxSumPow t (fun _ : Fin t => Q) S (fun u : ℤ => f (u + h) * star (f (u + h')))
        = ((boxNormPow t (fun _ : Fin t => Q) S
              (fun u : ℤ => f (u + h) * star (f (u + h'))) : ℝ) : ℂ) := by
    intro h h'
    refine BoxNorm.boxSumPow_eq_boxNormPow ht ?_
    have : (fun u : ℤ => f (u + h) * star (f (u + h'))) = dif h h' f := rfl
    rw [this]
    exact dif_finSuppZ hfin h h'
  have hsum_eq : (∑ h ∈ Q, ∑ h' ∈ Q,
        boxSumPow t (fun _ : Fin t => Q) S (fun u : ℤ => f (u + h) * star (f (u + h'))))
      = ((∑ h ∈ Q, ∑ h' ∈ Q,
          boxNormPow t (fun _ : Fin t => Q) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun h' _ => hinner h h')
  have hcast : ((Q.card : ℂ))⁻¹ * ((Q.card : ℂ))⁻¹ *
        ((∑ h ∈ Q, ∑ h' ∈ Q,
          boxNormPow t (fun _ : Fin t => Q) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) : ℝ) : ℂ)
      = ((((Q.card : ℝ))⁻¹ * ((Q.card : ℝ))⁻¹ *
          ∑ h ∈ Q, ∑ h' ∈ Q,
            boxNormPow t (fun _ : Fin t => Q) S
              (fun u : ℤ => f (u + h) * star (f (u + h')))) : ℝ) := by
    push_cast; ring
  have hnn : (0 : ℝ) ≤ ((Q.card : ℝ))⁻¹ * ((Q.card : ℝ))⁻¹ *
      ∑ h ∈ Q, ∑ h' ∈ Q, boxNormPow t (fun _ : Fin t => Q) S
        (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
    have h1 : (0 : ℝ) ≤ ((Q.card : ℝ))⁻¹ * ((Q.card : ℝ))⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ ∑ h ∈ Q, ∑ h' ∈ Q, boxNormPow t (fun _ : Fin t => Q) S
        (fun u : ℤ => f (u + h) * star (f (u + h'))) :=
      Finset.sum_nonneg (fun h _ => Finset.sum_nonneg (fun h' _ =>
        show (0 : ℝ) ≤ boxNormPow t (fun _ : Fin t => Q) S
          (fun u : ℤ => f (u + h) * star (f (u + h'))) from norm_nonneg _))
    exact mul_nonneg h1 h2
  rw [boxNormPow, hpeel, hsum_eq, hcast, Complex.norm_of_nonneg hnn]
  rw [show ((Q.card : ℝ))⁻¹ * ((Q.card : ℝ))⁻¹ = ((Q.card : ℝ))⁻¹ ^ 2 by ring]
  rfl



/-- **Base case of the rank induction (`rank 0`): no phase.**  For a function `G` supported in
`symIcc N` and `D ≥ 1`,

`‖∑' x, G x‖² ≤ (2(N+D)+1)·D⁻²·∑' x, ‖∑_{a ∈ arithIcc 1 D} G (x+a)‖²`. -/
theorem norm_tsum_sq_le_windowSum {D N : ℕ} (hD : 1 ≤ D) (G : ℤ → ℂ)
    (hsupp : SupportIn G N) :
    ‖∑' x : ℤ, G x‖ ^ 2
      ≤ (2 * ((N + D : ℕ) : ℝ) + 1) * ((D : ℝ))⁻¹ ^ 2
          * ∑' x : ℤ, ‖∑ a ∈ arithIcc 1 D, G (x + a)‖ ^ 2 := by
  classical
  have hD0 : (D : ℂ) ≠ 0 := by
    have : D ≠ 0 := by omega
    exact_mod_cast this
  set Z : ℤ → ℂ := fun x => ∑ a ∈ arithIcc 1 D, G (x + a) with hZdef
  -- `Z` vanishes off `symIcc (N+D)`
  have hZvan : ∀ x : ℤ, x ∉ symIcc (N + D) → Z x = 0 := by
    intro x hx
    rw [hZdef]
    refine Finset.sum_eq_zero (fun a ha => hsupp (x + a) ?_)
    obtain ⟨ha1, ha2⟩ := mem_arithIcc_one.mp ha
    have hxabs : (((N + D : ℕ)) : ℤ) < |x| := by
      by_contra h
      exact hx (by
        rw [symIcc, Finset.mem_Icc]
        have h' : |x| ≤ (((N + D : ℕ)) : ℤ) := not_lt.mp h
        rw [abs_le] at h'
        exact h')
    have hx' : (N : ℤ) + (D : ℤ) < |x| := by
      have : (((N + D : ℕ)) : ℤ) = (N : ℤ) + (D : ℤ) := by push_cast; ring
      rwa [this] at hxabs
    have h3 : |a| ≤ (D : ℤ) := by
      rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ a)]
      exact ha2
    have h4 : |x| ≤ |x + a| + |a| := by
      have h := abs_add_le (x + a) (-a)
      rw [show x + a + -a = x by ring, abs_neg] at h
      exact h
    have h2 : (N : ℤ) < |x + a| := by linarith
    have h5 : (N : ℤ) < (((x + a).natAbs : ℕ) : ℤ) := by rwa [Int.natCast_natAbs]
    exact_mod_cast h5
  have hZs : Summable Z := summable_of_ne_finset_zero (s := symIcc (N + D)) hZvan
  have hGvan : ∀ b : ℤ, b ∉ symIcc N → G b = 0 := by
    intro b hb
    refine hsupp b ?_
    by_contra h
    exact hb (by
      rw [symIcc, Finset.mem_Icc]
      have h' : |b| ≤ (N : ℤ) := by
        rw [abs_le]
        push_cast at h
        omega
      rw [abs_le] at h'
      exact h')
  have hGs : Summable G := summable_of_ne_finset_zero (s := symIcc N) hGvan
  -- the shift identity
  have hshift : (∑' x : ℤ, Z x) = (D : ℂ) * ∑' x : ℤ, G x := by
    rw [hZdef]
    rw [Summable.tsum_finsetSum (f := fun a x => G (x + a)) (s := arithIcc 1 D)
      (fun a _ => (Equiv.addRight a).summable_iff.mpr hGs)]
    have hterm : ∀ a : ℤ, (∑' x : ℤ, G (x + a)) = ∑' x : ℤ, G x := by
      intro a
      rw [← (Equiv.addRight a).tsum_eq G]
      rfl
    rw [Finset.sum_congr rfl (fun a _ => hterm a)]
    rw [Finset.sum_const, card_arithIcc_one, nsmul_eq_mul]
  -- the window sum is a finite sum over `symIcc (N+D)`
  have hZfin : (∑' x : ℤ, Z x) = ∑ x ∈ symIcc (N + D), Z x :=
    tsum_eq_sum (fun x hx => hZvan x hx)
  have hZnormsq : (∑' x : ℤ, ‖Z x‖ ^ 2) = ∑ x ∈ symIcc (N + D), ‖Z x‖ ^ 2 :=
    tsum_eq_sum (fun x hx => by rw [hZvan x hx]; simp)
  -- Cauchy–Schwarz
  have hcs : ‖∑ x ∈ symIcc (N + D), Z x‖ ^ 2
      ≤ ((symIcc (N + D)).card : ℝ) * ∑ x ∈ symIcc (N + D), ‖Z x‖ ^ 2 := by
    have h1 : ‖∑ x ∈ symIcc (N + D), Z x‖ ≤ ∑ x ∈ symIcc (N + D), ‖Z x‖ := norm_sum_le _ _
    have h2 := sq_sum_le_card_mul_sum_sq (s := symIcc (N + D)) (f := fun x => ‖Z x‖)
    have h3 : (0 : ℝ) ≤ ∑ x ∈ symIcc (N + D), ‖Z x‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    nlinarith [norm_nonneg (∑ x ∈ symIcc (N + D), Z x)]
  -- the identity `∑' G = D⁻¹ ∑' Z`
  have hnormG : ‖∑' x : ℤ, G x‖ = ((D : ℝ))⁻¹ * ‖∑' x : ℤ, Z x‖ := by
    have h : (∑' x : ℤ, G x) = ((D : ℂ))⁻¹ * ∑' x : ℤ, Z x := by
      rw [hshift]; field_simp
    rw [h, norm_mul, norm_inv, Complex.norm_natCast]
  rw [hnormG, hZfin, mul_pow, hZnormsq]
  have hfin : ((D : ℝ))⁻¹ ^ 2 * ‖∑ x ∈ symIcc (N + D), Z x‖ ^ 2
      ≤ (2 * ((N + D : ℕ) : ℝ) + 1) * ((D : ℝ))⁻¹ ^ 2
          * ∑ x ∈ symIcc (N + D), ‖Z x‖ ^ 2 := by
    have hcs' : ‖∑ x ∈ symIcc (N + D), Z x‖ ^ 2
        ≤ (2 * ((N + D : ℕ) : ℝ) + 1) * ∑ x ∈ symIcc (N + D), ‖Z x‖ ^ 2 := by
      rw [card_symIcc (N + D)] at hcs
      push_cast at hcs
      have hcast : 2 * ((N : ℝ) + (D : ℝ)) + 1 = 2 * ((N + D : ℕ) : ℝ) + 1 := by
        push_cast; ring
      rwa [hcast] at hcs
    have h1 : ((D : ℝ))⁻¹ ^ 2 * ‖∑ x ∈ symIcc (N + D), Z x‖ ^ 2
        ≤ ((D : ℝ))⁻¹ ^ 2 * (((2 * ((N + D : ℕ) : ℝ) + 1))
            * ∑ x ∈ symIcc (N + D), ‖Z x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcs' (by positivity)
    calc ((D : ℝ))⁻¹ ^ 2 * ‖∑ x ∈ symIcc (N + D), Z x‖ ^ 2
        ≤ ((D : ℝ))⁻¹ ^ 2 * (((2 * ((N + D : ℕ) : ℝ) + 1))
            * ∑ x ∈ symIcc (N + D), ‖Z x‖ ^ 2) := h1
      _ = (2 * ((N + D : ℕ) : ℝ) + 1) * ((D : ℝ))⁻¹ ^ 2
            * ∑ x ∈ symIcc (N + D), ‖Z x‖ ^ 2 := by ring
  exact hfin


/-! ## The `m = 1` step

The rank-lowering step for `m = 1` from the base case.  After splitting `u = (u₁,u')`,
`v = (v₁,v')` and fixing `(u,v')`, the phase `c := ψ₁(u,v)` is *constant* in the coordinate `v₁`
(exactly the blindness hypothesis), so the slice sum
`∑_{v₁∈Q} ‖∑_x H_{v₁}(x) e(c x)‖²` is the base case applied to the modulated functions
`x ↦ H_{v₁}(x) e(c x)`, and it lands on the `c`-chirped window sums.  Stated abstractly, with an
arbitrary index type `ι` in place of the `v₁`'s.

This is the honest shape of the `m = 1` step: it *consumes* the rank (the phase is now a single
constant `c` per slice) at the price of chirping the window sums.
-/

/-- **The `m = 1` step.**  For a family `H` supported in `symIcc N` and any frequency `c`,

`∑_i ‖∑' x, H_i x · e(c x)‖² ≤ (2(N+D)+1)·D⁻²·∑_i ∑' x, ‖∑_{a ∈ arithIcc 1 D} H_i (x+a) e(c a)‖²`.

Proof: the base case `norm_tsum_sq_le_windowSum` for the modulated functions
`x ↦ H_i x · e(c x)`, plus `e(c(x+a)) = e(cx)·e(ca)`. -/
theorem rankOne_step {D N : ℕ} (hD : 1 ≤ D) {ι : Type} [Fintype ι] (H : ι → ℤ → ℂ) (c : ℝ)
    (hsupp : ∀ i, SupportIn (H i) N) :
    ∑ i, ‖∑' x : ℤ, H i x * Complex.exp (2 * Real.pi * Complex.I * c * (x : ℝ))‖ ^ 2
      ≤ (2 * ((N + D : ℕ) : ℝ) + 1) * ((D : ℝ))⁻¹ ^ 2
          * ∑ i, ∑' x : ℤ, ‖∑ a ∈ arithIcc 1 D,
              H i (x + a) * Complex.exp (2 * Real.pi * Complex.I * c * (a : ℝ))‖ ^ 2 := by
  classical
  have hone : ∀ y : ℤ, ‖Complex.exp (2 * Real.pi * Complex.I * c * (y : ℝ))‖ = 1 := by
    intro y
    rw [Complex.norm_exp]
    simp
  have hpt : ∀ (i : ι) (x : ℤ),
      ‖∑ a ∈ arithIcc 1 D,
          H i (x + a) * Complex.exp (2 * Real.pi * Complex.I * c * ((x + a : ℤ) : ℝ))‖
        = ‖∑ a ∈ arithIcc 1 D,
            H i (x + a) * Complex.exp (2 * Real.pi * Complex.I * c * (a : ℝ))‖ := by
    intro i x
    have hfac : (∑ a ∈ arithIcc 1 D,
          H i (x + a) * Complex.exp (2 * Real.pi * Complex.I * c * ((x + a : ℤ) : ℝ)))
        = Complex.exp (2 * Real.pi * Complex.I * c * (x : ℝ))
            * ∑ a ∈ arithIcc 1 D,
                H i (x + a) * Complex.exp (2 * Real.pi * Complex.I * c * (a : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      push_cast
      rw [show (2 * ↑Real.pi * Complex.I * ↑c * (↑x + ↑a) : ℂ)
            = 2 * ↑Real.pi * Complex.I * ↑c * (↑x : ℂ) + 2 * ↑Real.pi * Complex.I * ↑c * (↑a : ℂ)
          by ring, Complex.exp_add]
      ring
    rw [hfac, norm_mul, hone x, one_mul]
  have hbase : ∀ i : ι,
      ‖∑' x : ℤ, H i x * Complex.exp (2 * Real.pi * Complex.I * c * (x : ℝ))‖ ^ 2
        ≤ (2 * ((N + D : ℕ) : ℝ) + 1) * ((D : ℝ))⁻¹ ^ 2
            * ∑' x : ℤ, ‖∑ a ∈ arithIcc 1 D,
                H i (x + a) * Complex.exp (2 * Real.pi * Complex.I * c * (a : ℝ))‖ ^ 2 := by
    intro i
    have hsuppc : SupportIn
        (fun y : ℤ => H i y * Complex.exp (2 * Real.pi * Complex.I * c * (y : ℝ))) N := by
      intro y hy
      simp [hsupp i y hy]
    have h := norm_tsum_sq_le_windowSum (D := D) (N := N) hD
      (fun y : ℤ => H i y * Complex.exp (2 * Real.pi * Complex.I * c * (y : ℝ))) hsuppc
    refine le_trans h (le_of_eq ?_)
    rw [tsum_congr (fun x => by rw [hpt i x])]
  calc ∑ i, ‖∑' x : ℤ, H i x * Complex.exp (2 * Real.pi * Complex.I * c * (x : ℝ))‖ ^ 2
      ≤ ∑ i, (2 * ((N + D : ℕ) : ℝ) + 1) * ((D : ℝ))⁻¹ ^ 2
            * ∑' x : ℤ, ‖∑ a ∈ arithIcc 1 D,
                H i (x + a) * Complex.exp (2 * Real.pi * Complex.I * c * (a : ℝ))‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => hbase i)
    _ = (2 * ((N + D : ℕ) : ℝ) + 1) * ((D : ℝ))⁻¹ ^ 2
          * ∑ i, ∑' x : ℤ, ‖∑ a ∈ arithIcc 1 D,
              H i (x + a) * Complex.exp (2 * Real.pi * Complex.I * c * (a : ℝ))‖ ^ 2 :=
        Finset.mul_sum _ _ _ |>.symm

end

end Work.Peluse.Ulower
