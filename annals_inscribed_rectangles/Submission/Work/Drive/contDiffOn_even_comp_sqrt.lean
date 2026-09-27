import Mathlib
import Submission.Work.Drive.iteratedDeriv_comp_sq
import Submission.Work.Drive.contDiff_iteratedDeriv_fst
import Submission.Work.Drive.esqSqrtParam

/-!
# The half-space Whitney factorisation (`√`-form)

`Work.Drive.contDiffOn_even_comp_sqrt`: a `C^∞` map `f : X × ℝ → E` which is even in its second
variable has, on `X × [0,∞)`, the same germ as a `C^∞` map of `(x, s) ↦ f (x, √s)`.

The proof (final line below) is the parametric even `√`-descent
`Work.Drive.contDiffOn_evenSqrtParam` from `Submission.Work.Drive.esqSqrtParam`, which is
self-contained modulo the quantitative flat descent `Work.Drive.contDiff_trunc_sqrt` and the flat
jet bound `Work.Drive.flat_bounds_of_jets`.  That module truncates the even Taylor expansion of `f`
in `t` at order `2m` and bounds the `√`-substitution of the remainder, which is flat to order
`2m + 2`.

The material below is the older, partially superseded route: `deriv_*` / `iteratedDeriv_parity`
record the parity of the iterated derivatives of an even function, and
`Work.Drive.exists_factorization_of_bricks` reduces the statement to a (refuted in general)
parametric Borel lemma plus a flat descent.  It is kept because the parity lemmas and the
reduction are still used elsewhere in the workspace.
-/

namespace Work.Drive

open scoped ContDiff

/-- If `g` is even then `deriv g` is odd. -/
lemma deriv_odd_of_even {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} (hg : ∀ t : ℝ, g (-t) = g t) (t : ℝ) : deriv g (-t) = - deriv g t := by
  have h := deriv_comp_neg (f := g) t
  rw [show (fun x : ℝ => g (-x)) = g from funext fun x => hg x] at h
  rw [h]
  simp

/-- If `g` is odd then `deriv g` is even. -/
lemma deriv_even_of_odd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} (hg : ∀ t : ℝ, g (-t) = - g t) (t : ℝ) : deriv g (-t) = deriv g t := by
  have h := deriv_comp_neg (f := g) t
  rw [show (fun x : ℝ => g (-x)) = fun x => - g x from funext fun x => hg x] at h
  have h2 : deriv (fun x : ℝ => - g x) t = - deriv g t := by simp
  rw [h2] at h
  exact (neg_injective h).symm

/-- Parity of the iterated derivatives of an even function. -/
lemma iteratedDeriv_parity {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} (hg : ∀ t : ℝ, g (-t) = g t) (j : ℕ) :
    (∀ t : ℝ, iteratedDeriv (2 * j) g (-t) = iteratedDeriv (2 * j) g t) ∧
      ∀ t : ℝ, iteratedDeriv (2 * j + 1) g (-t) = - iteratedDeriv (2 * j + 1) g t := by
  induction j with
  | zero =>
    refine ⟨fun t => ?_, fun t => ?_⟩
    · rw [show 2 * 0 = 0 by norm_num, iteratedDeriv_zero]
      exact hg t
    · rw [show 2 * 0 + 1 = 1 by norm_num, iteratedDeriv_one]
      exact deriv_odd_of_even hg t
  | succ k ih =>
    obtain ⟨hev, hod⟩ := ih
    have hev' : ∀ t : ℝ, iteratedDeriv (2 * (k + 1)) g (-t) =
        iteratedDeriv (2 * (k + 1)) g t := by
      intro t
      have hfun : iteratedDeriv (2 * (k + 1)) g = deriv (iteratedDeriv (2 * k + 1) g) := by
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, iteratedDeriv_succ]
      rw [hfun]
      exact deriv_even_of_odd hod t
    refine ⟨hev', fun t => ?_⟩
    have hfun : iteratedDeriv (2 * (k + 1) + 1) g = deriv (iteratedDeriv (2 * (k + 1)) g) :=
      iteratedDeriv_succ
    rw [hfun]
    exact deriv_odd_of_even hev' t

/-- All odd iterated derivatives of an even function vanish at the origin. -/
lemma iteratedDeriv_odd_eq_zero_of_even {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} (hg : ∀ t : ℝ, g (-t) = g t) (j : ℕ) :
    iteratedDeriv (2 * j + 1) g 0 = 0 := by
  have h : iteratedDeriv (2 * j + 1) g 0 = - iteratedDeriv (2 * j + 1) g 0 := by
    have h0 := (iteratedDeriv_parity hg j).2 0
    rwa [neg_zero] at h0
  have h2 : (2 : ℝ) • iteratedDeriv (2 * j + 1) g 0 = 0 := by
    rw [two_smul ℝ]
    nth_rewrite 1 [h]
    rw [neg_add_cancel]
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

end Work.Drive
namespace Work.Drive

open scoped ContDiff

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Assembly, parameterised by the four bricks.**

* `hA` : parametric Borel theorem (jet matching in the `s`-variable),
* `hB` : descent of a `t`-flat family,
* `hD` : the composition identity `(φ (·²))^{(2j)}(0) = (2j)!/j! · φ^{(j)}(0)`,
* `hG` : smoothness in `x` of the `t`-jets at `t = 0`. -/
theorem exists_factorization_of_bricks {f : X × ℝ → E}
    (hA : ∀ (c : ℕ → X → E), (∀ k : ℕ, ContDiff ℝ ∞ (c k)) →
      ∃ Q : X × ℝ → E, ContDiff ℝ ∞ Q ∧
        ∀ (x : X) (k : ℕ), iteratedDeriv k (fun s : ℝ => Q (x, s)) 0 = c k x)
    (hB : ∀ (R : X × ℝ → E), ContDiff ℝ ∞ R →
      (∀ (x : X) (k : ℕ), iteratedDeriv k (fun t : ℝ => R (x, t)) 0 = 0) →
      ∃ G : X × ℝ → E, ContDiff ℝ ∞ G ∧
        ∀ (x : X) (s : ℝ), 0 ≤ s → G (x, s) = R (x, Real.sqrt s))
    (hf : ContDiff ℝ ∞ f) (heven : ∀ (x : X) (t : ℝ), f (x, -t) = f (x, t)) :
    ∃ g : X × ℝ → E, ContDiffOn ℝ ∞ g (Set.univ ×ˢ Set.Ici (0 : ℝ)) ∧
      ∀ (x : X) (t : ℝ), 0 ≤ t → g (x, t) = f (x, Real.sqrt t) := by
  -- the jet-matching coefficient family
  let c : ℕ → X → E := fun k x =>
    ((Nat.factorial k : ℝ) / (Nat.factorial (2 * k) : ℝ)) •
      iteratedDeriv (2 * k) (fun t : ℝ => f (x, t)) 0
  have hc : ∀ k : ℕ, ContDiff ℝ ∞ (c k) := by
    intro k
    exact (contDiff_iteratedDeriv_fst hf (2 * k)).const_smul _
  obtain ⟨Q, hQ, hQjet⟩ := hA c hc
  -- the polynomial part and the flat remainder
  let P : X × ℝ → E := fun p => Q (p.1, p.2 ^ 2)
  have hP : ContDiff ℝ ∞ P := by
    have h2 : ContDiff ℝ ∞ (fun p : X × ℝ => p.2 ^ 2) := contDiff_snd.pow 2
    have hpair : ContDiff ℝ ∞ (fun p : X × ℝ => (p.1, p.2 ^ 2)) := contDiff_fst.prodMk h2
    exact hQ.comp hpair
  let R : X × ℝ → E := fun p => f p - P p
  have hR : ContDiff ℝ ∞ R := hf.sub hP
  -- the remainder is flat in `t` at `t = 0`
  have hflat : ∀ (x : X) (k : ℕ), iteratedDeriv k (fun t : ℝ => R (x, t)) 0 = 0 := by
    intro x k
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- even case: k = j + j, rewrite to 2 * j
      have hk : j + j = 2 * j := by omega
      rw [hj, hk]
      have hfx : ContDiff ℝ ∞ (fun t : ℝ => f (x, t)) :=
        hf.comp (contDiff_const.prodMk contDiff_id)
      have hPx : ContDiff ℝ ∞ (fun t : ℝ => P (x, t)) :=
        hP.comp (contDiff_const.prodMk contDiff_id)
      have hsub : iteratedDeriv (2 * j) (fun t : ℝ => R (x, t)) 0 =
          iteratedDeriv (2 * j) (fun t : ℝ => f (x, t)) 0 -
            iteratedDeriv (2 * j) (fun t : ℝ => P (x, t)) 0 := by
        have hfun : (fun t : ℝ => R (x, t)) =
            (fun t : ℝ => f (x, t)) - (fun t : ℝ => P (x, t)) := rfl
        rw [hfun, iteratedDeriv_sub
          (hfx.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
          (hPx.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
      rw [hsub]
      have hPjet : iteratedDeriv (2 * j) (fun t : ℝ => P (x, t)) 0 =
          ((Nat.factorial (2 * j) : ℝ) / (Nat.factorial j : ℝ)) •
            iteratedDeriv j (fun s : ℝ => Q (x, s)) 0 := by
        have hφ : ContDiff ℝ ∞ (fun s : ℝ => Q (x, s)) :=
          hQ.comp (contDiff_const.prodMk contDiff_id)
        exact iteratedDeriv_comp_sq hφ j
      rw [hPjet, hQjet x j]
      simp only [c]
      rw [smul_smul]
      have hfac : ((Nat.factorial (2 * j) : ℝ) / (Nat.factorial j : ℝ)) *
          ((Nat.factorial j : ℝ) / (Nat.factorial (2 * j) : ℝ)) = 1 := by
        field_simp
      rw [hfac, one_smul, sub_self]
    · -- odd case: k = 2 * j + 1
      subst hj
      have hReven : ∀ t : ℝ, (fun t : ℝ => R (x, t)) (-t) = (fun t : ℝ => R (x, t)) t := by
        intro t
        show R (x, -t) = R (x, t)
        simp only [R, Pi.sub_apply, P]
        rw [neg_sq, heven x t]
      exact iteratedDeriv_odd_eq_zero_of_even hReven j
  obtain ⟨G, hGc, hGval⟩ := hB R hR hflat
  refine ⟨fun p => Q p + G p, (hQ.add hGc).contDiffOn, fun x t ht => ?_⟩
  have hsq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
  have h1 : G (x, t) = R (x, Real.sqrt t) := hGval x t ht
  simp only [Pi.add_apply]
  rw [h1]
  simp only [R, Pi.sub_apply, P]
  rw [hsq]
  abel

end Work.Drive

namespace Work.Drive

open scoped ContDiff

/-- **TARGET.**  `Work.Drive.contDiffOn_even_comp_sqrt`.

A `C^∞` map `f : X × ℝ → E` which is even in its second variable agrees on the closed half-space
`X × [0, ∞)` with the `C^∞` function `(x, s) ↦ f (x, √s)`.

The witness is the descent itself; its smoothness on the half-space is
`Work.Drive.contDiffOn_evenSqrtParam` (`Submission.Work.Drive.esqSqrtParam`). -/
theorem contDiffOn_even_comp_sqrt {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : X × ℝ → E}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (heven : ∀ (x : X) (t : ℝ), f (x, -t) = f (x, t)) :
    ∃ g : X × ℝ → E,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (Set.univ ×ˢ Set.Ici (0 : ℝ)) ∧
      ∀ (x : X) (t : ℝ), 0 ≤ t → g (x, t) = f (x, Real.sqrt t) :=
  ⟨fun p => f (p.1, Real.sqrt p.2), contDiffOn_evenSqrtParam hf heven, fun x t _ => rfl⟩

end Work.Drive
