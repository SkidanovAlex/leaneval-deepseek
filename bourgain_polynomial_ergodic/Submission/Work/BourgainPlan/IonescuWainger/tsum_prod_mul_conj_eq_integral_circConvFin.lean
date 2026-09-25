import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FreqArc
import Submission.Work.BourgainPlan.IonescuWainger.tsum_mul_conj_eq_integral_discFourier
import Submission.Work.BourgainPlan.IonescuWainger.discFourier_mul_eq_circConv

open MeasureTheory Finset
open scoped BigOperators

namespace Work.BourgainPlan.IonescuWainger

/-- A finite product of finitely supported functions on `ℤ` is finitely supported. -/
private lemma finite_support_finprod {n : ℕ} (f : Fin (n + 1) → ℤ → ℂ)
    (hf : ∀ i, (Function.support (f i)).Finite) :
    (Function.support (fun m => ∏ i, f i m)).Finite := by
  refine (hf 0).subset fun m hm => ?_
  intro h0
  exact (Function.mem_support.mp hm) (Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (n + 1))) h0)

/-- **The Fourier transform of a finite product is the iterated convolution of the transforms.**
For finitely supported `f i : ℤ → ℂ` (`i : Fin (n+1)`) and every `ξ : 𝕋 = ℝ/ℤ`,

`𝓕 (∏_i f i) ξ = (✻_i 𝓕(f i)) ξ`,

where `discFourier h ξ = ∑'_m h m · e^{2πi m ξ}` and `circConvFin (n+1) F` is the iterated circle
convolution of `FreqArc.lean`.  This iterates the two-factor identity
`discFourier_mul_eq_circConv` by induction on `n`. -/
private lemma discFourier_finprod_eq_circConvFin : ∀ n,
    ∀ (f : Fin (n + 1) → ℤ → ℂ), (∀ i, (Function.support (f i)).Finite) →
      ∀ ξ : Circle,
        discFourier (fun m => ∏ i, f i m) ξ
          = circConvFin (n + 1) (fun i => discFourier (f i)) ξ := by
  intro n
  induction n with
  | zero =>
      intro f hf ξ
      have h1 : (fun m : ℤ => ∏ i : Fin 1, f i m) = f 0 := by
        funext m
        exact Fin.prod_univ_one fun i : Fin 1 => f i m
      rw [h1]
      rfl
  | succ n ih =>
      intro f hf ξ
      have hsplit : (fun m : ℤ => ∏ i : Fin (n + 1 + 1), f i m)
          = fun m : ℤ =>
              (∏ i : Fin (n + 1), f (Fin.castSucc i) m) * f (Fin.last (n + 1)) m := by
        funext m
        exact Fin.prod_univ_castSucc fun i : Fin (n + 1 + 1) => f i m
      have hf1 : (Function.support
          (fun m => ∏ i : Fin (n + 1), f (Fin.castSucc i) m)).Finite :=
        finite_support_finprod (fun i : Fin (n + 1) => f (Fin.castSucc i))
          (fun i => hf (Fin.castSucc i))
      rw [hsplit, discFourier_mul_eq_circConv hf1 (hf (Fin.last (n + 1))) ξ]
      have hih : discFourier (fun m => ∏ i : Fin (n + 1), f (Fin.castSucc i) m)
          = circConvFin (n + 1) (fun i => discFourier (f (Fin.castSucc i))) :=
        funext fun ξ => ih (fun i : Fin (n + 1) => f (Fin.castSucc i))
          (fun i => hf (Fin.castSucc i)) ξ
      rw [hih]
      rfl

/-- **The pairing of two families of finitely supported functions is the pairing of their convolved
Fourier transforms.**  For finitely supported `f i, g i : ℤ → ℂ` (`i : Fin (n+1)`),

`∑_m (∏_i f i m) · conj (∏_i g i m) = ∫_𝕋 (✻_i 𝓕(f i))(ξ) · conj ((✻_i 𝓕(g i))(ξ)) dξ`,

where `discFourier h ξ = ∑'_m h m · e^{2πi m ξ}`, `circConvFin` is the iterated circle convolution
and the integral is against the probability Haar measure `AddCircle.haarAddCircle`.

This is the complete Fourier-side reduction of the superorthogonality hypothesis used by
`superorthogonal_khintchine` for a finitely supported major-arc system: combined with the vanishing
of the right-hand side supplied by `integral_circConvFin_mul_conj_eq_zero_of_nonce_of_good` (from
`FreqArc.lean`), it gives, for every nonce tuple,

`Σ_m ∏_i ⟨f_i(m), g_i(m)⟩ = 0`,

which is exactly Tao's `ortho`(ii)/(iii) (arXiv:2008.05066, §4). -/
theorem tsum_prod_mul_conj_eq_integral_circConvFin {n : ℕ} (f g : Fin (n + 1) → ℤ → ℂ)
    (hf : ∀ i, (Function.support (f i)).Finite) (hg : ∀ i, (Function.support (g i)).Finite) :
    ∑' m : ℤ, (∏ i, f i m) * star (∏ i, g i m)
      = ∫ ξ : Circle, circConvFin (n + 1) (fun i => discFourier (f i)) ξ
          * star (circConvFin (n + 1) (fun i => discFourier (g i)) ξ)
          ∂AddCircle.haarAddCircle := by
  have hF : (Function.support (fun m => ∏ i, f i m)).Finite :=
    finite_support_finprod f hf
  have hG : (Function.support (fun m => ∏ i, g i m)).Finite :=
    finite_support_finprod g hg
  rw [tsum_mul_conj_eq_integral_discFourier hF hG]
  rw [show (fun ξ : Circle => discFourier (fun m => ∏ i, f i m) ξ
          * star (discFourier (fun m => ∏ i, g i m) ξ))
        = fun ξ : Circle => circConvFin (n + 1) (fun i => discFourier (f i)) ξ
          * star (circConvFin (n + 1) (fun i => discFourier (g i)) ξ) from
      funext fun ξ => by
        rw [discFourier_finprod_eq_circConvFin n f hf ξ,
          discFourier_finprod_eq_circConvFin n g hg ξ]]

end Work.BourgainPlan.IonescuWainger
