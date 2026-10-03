import Mathlib
import Submission.Work.A3.Defs
import Submission.Work.A3.integral_ech_char
import Submission.Work.A3.norm_pow_two_mul

/-!
# `Work.A3.moment_identity`

The `2k`-th moment of the normalised polynomial exponential sum
`m_N(θ) = N⁻¹ ∑_{1 ≤ n ≤ N} e(-2πi θ Q(n))` is `N^{-2k}` times the `k`-fold energy of the
polynomial sequence `Q(1),…,Q(N)`:

  `∫₀¹ ‖m_N(θ)‖^{2k} dθ = N^{-2k} · #{(n⃗,m⃗) ∈ [1,N]^k × [1,N]^k : ∑ᵢ Q(nᵢ) = ∑ⱼ Q(mⱼ)}`.

This is the arithmetic input of Krause–Mirek–Tao's `lp-improv` (see `Submission/Work/A3/Defs.lean`);
the identity is proved by expanding the `2k`-th power into a double sum over `k`-tuples, applying
the orthogonality of the characters `θ ↦ e(-2πiMθ)` on `[0,1]` (`Work.A3.integral_ech_char`) and
counting the surviving pairs (`Work.A3.polyEnergy`).
-/

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The additive character `θ ↦ e(-2πi M θ)`. -/
def ECH (M : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (M : ℂ)) * θ)

lemma integral_ECH (M : ℤ) : ∫ θ in Set.Icc (0:ℝ) 1, ECH M θ = if M = 0 then (1 : ℂ) else 0 :=
  integral_ech_char M

lemma ECH_zero (θ : ℝ) : ECH 0 θ = 1 := by simp [ECH]

lemma ECH_add (M L : ℤ) (θ : ℝ) : ECH (M + L) θ = ECH M θ * ECH L θ := by
  simp only [ECH]
  rw [show -(2 * (Real.pi : ℂ) * Complex.I * ((M + L : ℤ) : ℂ)) * θ
        = (-(2 * (Real.pi : ℂ) * Complex.I * (M : ℂ)) * θ) + (-(2 * (Real.pi : ℂ) * Complex.I * (L : ℂ)) * θ) from by
      push_cast; ring]
  rw [Complex.exp_add]

lemma ECH_conj (M : ℤ) (θ : ℝ) : (starRingEnd ℂ) (ECH M θ) = ECH (-M) θ := by
  have hM : (starRingEnd ℂ) ((M : ℤ) : ℂ) = ((M : ℤ) : ℂ) := by
    rw [← Complex.ofReal_intCast, Complex.conj_ofReal]
  rw [ECH, ← Complex.exp_conj, ECH]
  congr 1
  simp only [map_mul, map_neg, map_ofNat, hM, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

lemma ECH_prod {ι : Type*} (s : Finset ι) (a : ι → ℤ) (θ : ℝ) :
    ∏ i ∈ s, ECH (a i) θ = ECH (∑ i ∈ s, a i) θ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ECH_zero]
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ECH_add, ih]

lemma ECH_pair {k : ℕ} (g : ℤ → ℤ) (θ : ℝ) (v w : Fin k → ℤ) :
    (∏ i : Fin k, ECH (g (v i)) θ) * (starRingEnd ℂ) (∏ i : Fin k, ECH (g (w i)) θ)
      = ECH ((∑ i : Fin k, g (v i)) - (∑ i : Fin k, g (w i))) θ := by
  have h1 : (∏ i : Fin k, ECH (g (v i)) θ) = ECH (∑ i : Fin k, g (v i)) θ := ECH_prod _ _ _
  have h2 : (starRingEnd ℂ) (∏ i : Fin k, ECH (g (w i)) θ)
      = ECH (-(∑ i : Fin k, g (w i))) θ := by
    rw [map_prod]
    simp only [ECH_conj]
    rw [ECH_prod, Finset.sum_neg_distrib]
  rw [h1, h2, ← ECH_add, sub_eq_add_neg]

lemma integrable_ECH (M : ℤ) :
    Integrable (fun θ : ℝ => ECH M θ) (volume.restrict (Set.Icc (0:ℝ) 1)) := by
  have hc : Continuous fun θ : ℝ => ECH M θ := by
    simp only [ECH]; fun_prop
  exact hc.integrableOn_Icc

lemma sum_Icc_natCast (N : ℕ) (f : ℤ → ℂ) :
    ∑ n ∈ Finset.Icc 1 N, f (n : ℤ) = ∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), f m := by
  have h : (Finset.Icc (1:ℤ) (N:ℤ)) = (Finset.Icc 1 N).image (fun n : ℕ => (n:ℤ)) := by
    ext m
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨m.toNat, ⟨by omega, by omega⟩, Int.toNat_of_nonneg (by omega)⟩
    · rintro ⟨n, ⟨h1, h2⟩, rfl⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  rw [h, Finset.sum_image (fun x _ y _ hxy => by exact_mod_cast hxy)]

theorem moment_aux (g : ℤ → ℤ) (N k : ℕ) :
    ∫ θ in Set.Icc (0:ℝ) 1, ‖∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ‖ ^ (2 * k)
      = (((Finset.product (Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ)))
          (Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ)))).filter
          (fun p => (∑ i, g (p.1 i)) = (∑ i, g (p.2 i)))).card : ℝ) := by
  have hpt : ∀ θ : ℝ,
      ((∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ) ^ k) *
        (starRingEnd ℂ) ((∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ) ^ k)
      = ∑ v ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ)),
          ∑ w ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ)),
            (∏ i : Fin k, ECH (g (v i)) θ) *
              (starRingEnd ℂ) (∏ i : Fin k, ECH (g (w i)) θ) := by
    intro θ
    rw [Finset.sum_pow' (Finset.Icc (1:ℤ) (N:ℤ)) (fun m => ECH (g m) θ) k]
    rw [map_sum]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  have hpt' : ∀ θ : ℝ,
      ((∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ) ^ k) *
        (starRingEnd ℂ) ((∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ) ^ k)
      = ∑ p ∈ Finset.product (Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ)))
              (Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ))),
          (∏ i : Fin k, ECH (g (p.1 i)) θ) *
            (starRingEnd ℂ) (∏ i : Fin k, ECH (g (p.2 i)) θ) := by
    intro θ
    rw [hpt θ]
    exact (Finset.sum_product _ _
      (f := fun p : (Fin k → ℤ) × (Fin k → ℤ) =>
        (∏ i : Fin k, ECH (g (p.1 i)) θ) *
          (starRingEnd ℂ) (∏ i : Fin k, ECH (g (p.2 i)) θ))).symm
  have hint : ∀ (p : (Fin k → ℤ) × (Fin k → ℤ)),
      Integrable (fun θ : ℝ => (∏ i : Fin k, ECH (g (p.1 i)) θ) *
        (starRingEnd ℂ) (∏ i : Fin k, ECH (g (p.2 i)) θ)) (volume.restrict (Set.Icc (0:ℝ) 1)) := by
    intro p
    rw [show (fun θ : ℝ => (∏ i : Fin k, ECH (g (p.1 i)) θ) *
        (starRingEnd ℂ) (∏ i : Fin k, ECH (g (p.2 i)) θ))
        = fun θ : ℝ => ECH ((∑ i : Fin k, g (p.1 i)) - (∑ i : Fin k, g (p.2 i))) θ from
      funext (fun θ => ECH_pair g θ p.1 p.2)]
    exact integrable_ECH _
  have hint2 : Integrable (fun θ : ℝ =>
      ((∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ) ^ k) *
        (starRingEnd ℂ) ((∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ) ^ k))
      (volume.restrict (Set.Icc (0:ℝ) 1)) := by
    rw [show (fun θ : ℝ => ((∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ) ^ k) *
        (starRingEnd ℂ) ((∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ) ^ k))
        = fun θ : ℝ => ∑ p ∈ Finset.product (Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ)))
              (Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ))),
          (∏ i : Fin k, ECH (g (p.1 i)) θ) *
            (starRingEnd ℂ) (∏ i : Fin k, ECH (g (p.2 i)) θ) from funext hpt']
    exact integrable_finsetSum _ (fun p hp => hint p)
  have key : ∫ θ in Set.Icc (0:ℝ) 1,
      ((∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ) ^ k) *
        (starRingEnd ℂ) ((∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ) ^ k)
      = ∑ p ∈ Finset.product (Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ)))
              (Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ))),
          if (∑ i : Fin k, g (p.1 i)) = (∑ i : Fin k, g (p.2 i)) then (1 : ℂ) else 0 := by
    rw [show (fun θ : ℝ => ((∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ) ^ k) *
        (starRingEnd ℂ) ((∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ) ^ k))
        = fun θ : ℝ => ∑ p ∈ Finset.product (Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ)))
              (Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ))),
          (∏ i : Fin k, ECH (g (p.1 i)) θ) *
            (starRingEnd ℂ) (∏ i : Fin k, ECH (g (p.2 i)) θ) from funext hpt']
    rw [integral_finsetSum _ (fun p hp => hint p)]
    apply Finset.sum_congr rfl
    intro p hp
    rw [show (fun θ : ℝ => (∏ i : Fin k, ECH (g (p.1 i)) θ) *
        (starRingEnd ℂ) (∏ i : Fin k, ECH (g (p.2 i)) θ))
        = fun θ : ℝ => ECH ((∑ i : Fin k, g (p.1 i)) - (∑ i : Fin k, g (p.2 i))) θ from
      funext (fun θ => ECH_pair g θ p.1 p.2)]
    rw [integral_ECH]
    simp only [sub_eq_zero]
  calc ∫ θ in Set.Icc (0:ℝ) 1, ‖∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ‖ ^ (2 * k)
      = ∫ θ in Set.Icc (0:ℝ) 1,
          (((∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ) ^ k) *
            (starRingEnd ℂ) ((∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (g m) θ) ^ k)).re := by
        simp_rw [norm_pow_two_mul]
    _ = ((∑ p ∈ Finset.product (Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ)))
              (Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ))),
          if (∑ i : Fin k, g (p.1 i)) = (∑ i : Fin k, g (p.2 i)) then (1 : ℂ) else 0)).re := by
        refine (integral_re hint2).trans ?_
        rw [key]
        rfl
    _ = (((Finset.product (Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ)))
              (Fintype.piFinset (fun _ : Fin k => Finset.Icc (1:ℤ) (N:ℤ)))).filter
          (fun p => (∑ i, g (p.1 i)) = (∑ i, g (p.2 i)))).card : ℝ) := by
        rw [Finset.sum_boole]
        simp

theorem moment_identity (Q : Polynomial ℤ) (N k : ℕ) (hN : 1 ≤ N) : MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) (fun θ : ℝ => ‖Work.A3.kmtMul Q N θ‖ ^ (2 * k)) = ((N : ℝ) ^ (2 * k))⁻¹ * (Work.A3.polyEnergy Q k N : ℝ) := by
  have hsum : ∀ θ : ℝ, (∑ n ∈ Finset.Icc 1 N, ECH (Q.eval (n : ℤ)) θ)
      = ∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (Q.eval m) θ :=
    fun θ => sum_Icc_natCast N (fun m => ECH (Q.eval m) θ)
  have hkmt : ∀ θ : ℝ, kmtMul Q N θ
      = (N : ℂ)⁻¹ * (∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (Q.eval m) θ) := by
    intro θ
    rw [kmtMul]
    congr 1
    rw [← hsum θ]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [ECH]
    congr 1
    push_cast
    ring
  have hnorm : ∀ θ : ℝ, ‖kmtMul Q N θ‖ ^ (2 * k)
      = ((N : ℝ) ^ (2 * k))⁻¹ * ‖∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), ECH (Q.eval m) θ‖ ^ (2 * k) := by
    intro θ
    rw [hkmt θ, norm_mul, norm_inv, Complex.norm_natCast, mul_pow, inv_pow]
  simp_rw [hnorm]
  rw [MeasureTheory.integral_const_mul,
    moment_aux (fun m => Q.eval m) N k]
  congr 1

end
end Work.A3
