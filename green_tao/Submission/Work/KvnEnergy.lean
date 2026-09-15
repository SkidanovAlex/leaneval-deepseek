import Submission.Work.FinSigma

set_option linter.unusedSectionVars false

/-!
# The Furstenberg tower step with exceptional sets (Green–Tao §7)

Abstract conditional-expectation lemmas needed for the *Iterative Step*
(Green–Tao Proposition 7.2) in the proof of the generalised Koopman–von Neumann
structure theorem.

Compared with the plain energy-increment identity, the refinement step is here
only carried out *outside an exceptional set*: the conditional expectations are
weighted by `(1 - 1_Ω)`, and the exceptional sets `Ω ⊆ Ω'` are unions of atoms
of the coarser resp. finer σ-algebra.
-/

open Finset

namespace FinSigma

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `Ω` is `part`-saturated, i.e. a union of atoms of the σ-algebra presented by `part`. -/
def Sat (part : X → Finset X) (Ω : Finset X) : Prop := ∀ x ∈ Ω, part x ⊆ Ω

lemma Sat.subset {part : X → Finset X} {Ω : Finset X} (h : Sat part Ω) {x : X}
    (hx : x ∈ Ω) : part x ⊆ Ω := h x hx

/-- Summing over the complement of `Ω` is summing the indicator of the complement. -/
lemma sum_sdiff_univ {Ω : Finset X} (f : X → ℝ) :
    ∑ x ∈ Finset.univ \ Ω, f x = ∑ x, (if x ∈ Ω then (0 : ℝ) else 1) * f x := by
  have h : (Finset.univ \ Ω) = Finset.univ.filter (fun x => x ∉ Ω) := by
    ext x; simp
  rw [h, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ Ω <;> simp [hx]

lemma isMeas_const (part : X → Finset X) (c : ℝ) : IsMeas part (fun _ : X => c) :=
  fun _ _ _ => rfl

lemma isMeas_ind {part : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) {Ω : Finset X} (hΩ : Sat part Ω) :
    IsMeas part (fun x => if x ∈ Ω then (1 : ℝ) else 0) := by
  intro x y hy
  by_cases hx : x ∈ Ω
  · have hy' : y ∈ Ω := hΩ x hx hy
    simp only [hx, hy', if_true]
  · have hy' : y ∉ Ω := by
      intro hyy
      have hpy : part y = part x := heq x y hy
      have hsub := hΩ y hyy
      rw [hpy] at hsub
      exact hx (hsub (hmem x))
    simp only [hx, hy', if_false]

lemma isMeas_neg {part : X → Finset X} {f : X → ℝ} (hf : IsMeas part f) :
    IsMeas part (fun x => -f x) := fun x y hy => by simp only [hf x y hy]

lemma isMeas_add {part : X → Finset X} {f g : X → ℝ} (hf : IsMeas part f)
    (hg : IsMeas part g) : IsMeas part (fun x => f x + g x) :=
  fun x y hy => by simp only [hf x y hy, hg x y hy]

lemma isMeas_sub {part : X → Finset X} {f g : X → ℝ} (hf : IsMeas part f)
    (hg : IsMeas part g) : IsMeas part (fun x => f x - g x) :=
  fun x y hy => by simp only [hf x y hy, hg x y hy]

lemma isMeas_mul {part : X → Finset X} {f g : X → ℝ} (hf : IsMeas part f)
    (hg : IsMeas part g) : IsMeas part (fun x => f x * g x) :=
  fun x y hy => by simp only [hf x y hy, hg x y hy]

lemma isMeas_ind_compl {part : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) {Ω : Finset X} (hΩ : Sat part Ω) :
    IsMeas part (fun x => if x ∈ Ω then (0 : ℝ) else 1) := by
  have h := isMeas_ind hmem heq hΩ
  have h' : (fun x : X => (1 : ℝ) - (if x ∈ Ω then (1 : ℝ) else 0))
      = (fun x : X => if x ∈ Ω then (0 : ℝ) else 1) := by
    funext x; by_cases hx : x ∈ Ω <;> simp [hx]
  rw [← h']
  exact isMeas_sub (part := part) (isMeas_const part 1) h


/-- A sum weighted by the indicator of `S` is the sum over `S`. -/
lemma sum_indicator_eq {S : Finset X} (u : X → ℝ) :
    ∑ x, (if x ∈ S then (1 : ℝ) else 0) * u x = ∑ x ∈ S, u x := by
  have h : Finset.univ.filter (fun x => x ∈ S) = S := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hpoint : ∀ x : X, (if x ∈ S then (1 : ℝ) else 0) * u x
      = (if x ∈ S then u x else 0) := by
    intro x; by_cases hx : x ∈ S <;> simp [hx]
  simp only [hpoint]
  rw [← Finset.sum_filter (s := Finset.univ) (p := fun x => x ∈ S) (f := u), h]

/-- A sum weighted by the indicator of the complement of `S` is the sum over `univ \ S`. -/
lemma sum_ind_compl_eq {S : Finset X} (u : X → ℝ) :
    ∑ x, (if x ∈ S then (0 : ℝ) else 1) * u x = ∑ x ∈ Finset.univ \ S, u x :=
  (sum_sdiff_univ (Ω := S) u).symm

/-- The indicator of the annulus `Ω' \ Ω` for `Ω ⊆ Ω'`. -/
lemma ind_diff {Ω Ω' : Finset X} (hsub : Ω ⊆ Ω') (x : X) :
    ((if x ∈ Ω' then (0 : ℝ) else 1) - (if x ∈ Ω then (0 : ℝ) else 1))
      = - (if x ∈ Ω' \ Ω then (1 : ℝ) else 0) := by
  have hmem : (x ∈ Ω' \ Ω) ↔ (x ∈ Ω' ∧ x ∉ Ω) := by simp [Finset.mem_sdiff]
  by_cases h2 : x ∈ Ω
  · have h1 : x ∈ Ω' := hsub h2
    have h3 : ¬ (x ∈ Ω' \ Ω) := by rw [hmem]; exact fun h => h.2 h2
    rw [if_pos h1, if_pos h2, if_neg h3]; norm_num
  · by_cases h1 : x ∈ Ω'
    · have h3 : x ∈ Ω' \ Ω := by rw [hmem]; exact ⟨h1, h2⟩
      rw [if_pos h1, if_neg h2, if_pos h3]; norm_num
    · have h3 : ¬ (x ∈ Ω' \ Ω) := by rw [hmem]; exact fun h => h1 h.1
      rw [if_neg h1, if_neg h2, if_neg h3]; norm_num

/-- A sum weighted by the indicator of the annulus `Ω' \ Ω` is the sum over the annulus. -/
lemma sum_ind_diff_eq {Ω Ω' : Finset X} (hsub : Ω ⊆ Ω') (u : X → ℝ) :
    ∑ x, ((if x ∈ Ω' then (0 : ℝ) else 1) - (if x ∈ Ω then (0 : ℝ) else 1)) * u x
      = - ∑ x ∈ Ω' \ Ω, u x := by
  have hpoint : ∀ x : X,
      ((if x ∈ Ω' then (0 : ℝ) else 1) - (if x ∈ Ω then (0 : ℝ) else 1)) * u x
        = - ((if x ∈ Ω' \ Ω then (1 : ℝ) else 0) * u x) := by
    intro x; rw [ind_diff hsub x]; ring
  simp only [hpoint, Finset.sum_neg_distrib]
  rw [sum_indicator_eq u]

/-- Self-adjointness of the conditional expectation on a saturated set. -/
lemma sum_cE_mul_of_sat {part : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) {Ω : Finset X} (hΩ : Sat part Ω)
    (f h : X → ℝ) (hh : IsMeas part h) :
    ∑ x ∈ Ω, cE part f x * h x = ∑ x ∈ Ω, f x * h x :=
  sum_cE_mul_measurable_of_union hmem heq Ω hΩ f h hh


/-- A saturated set of a finer σ-algebra is saturated for it too. -/
lemma Sat.of_refines {P Q : X → Finset X} (href : ∀ x, Q x ⊆ P x) {Ω : Finset X}
    (h : Sat P Ω) : Sat Q Ω := fun x hx y hy => h x hx (href x hy)

/-- The difference of two saturated sets is saturated. -/
lemma Sat.sdiff {part : X → Finset X} (heq : ∀ x y : X, y ∈ part x → part y = part x)
    (hmem : ∀ x, x ∈ part x) {Ω Ω' : Finset X} (hΩ : Sat part Ω) (hΩ' : Sat part Ω') :
    Sat part (Ω' \ Ω) := by
  intro x hx y hy
  rw [Finset.mem_sdiff] at hx ⊢
  refine ⟨hΩ' x hx.1 hy, fun hyΩ => hx.2 ?_⟩
  have hsub := hΩ y hyΩ
  have hpy : part y = part x := heq x y hy
  rw [hpy] at hsub
  exact hsub (hmem x)

/-- **Orthogonality of the `Ω`-residual against the refinement difference.**
If `Ω` is `P`-saturated and `Q` refines `P`, the complement-weighted residual
`(1 - 1_Ω)·𝔼(f|P)` is orthogonal to `𝔼(f|Q) - 𝔼(f|P)`. -/
lemma sum_ind_compl_mul_cE_sub {P Q : X → Finset X} (hPmem : ∀ x, x ∈ P x)
    (hPeq : ∀ x y : X, y ∈ P x → P y = P x) (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) (href : ∀ x, Q x ⊆ P x)
    {Ω : Finset X} (hΩ : Sat P Ω) (f : X → ℝ) :
    ∑ x, (if x ∈ Ω then (0 : ℝ) else 1) * (cE P f x * (cE Q f x - cE P f x)) = 0 := by
  set u : X → ℝ := fun x => (if x ∈ Ω then (0 : ℝ) else 1) * cE P f x with hu
  have hAQ : IsMeas Q (cE P f) := fun x y hy => cE_measurable hPeq f x y (href x hy)
  have huP : IsMeas P u :=
    isMeas_mul (isMeas_ind_compl hPmem hPeq hΩ) (cE_measurable hPeq f)
  have huQ : IsMeas Q u :=
    isMeas_mul (isMeas_ind_compl hQmem hQeq (Sat.of_refines href hΩ)) hAQ
  have e : ∀ x : X,
      (if x ∈ Ω then (0 : ℝ) else 1) * (cE P f x * (cE Q f x - cE P f x))
        = u x * (cE Q f x - cE P f x) := by
    intro x; simp only [hu]; ring
  simp only [e]
  have hsplit : ∑ x, u x * (cE Q f x - cE P f x)
      = ∑ x, u x * cE Q f x - ∑ x, u x * cE P f x := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hsplit]
  have h1 : ∑ x, u x * cE Q f x = ∑ x, cE Q f x * u x :=
    Finset.sum_congr rfl fun x _ => by ring
  have h2 : ∑ x, u x * cE P f x = ∑ x, cE P f x * u x :=
    Finset.sum_congr rfl fun x _ => by ring
  rw [h1, h2, sum_cE_mul_measurable hQmem hQeq f u huQ,
    sum_cE_mul_measurable hPmem hPeq f u huP]
  ring

/-- **Restriction reduction.**  For `Q` refining `P` and `Ω` `Q`-saturated, the pairing of
the `Ω`-residual `f - 𝔼(f|P)` with a `Q`-measurable weight only sees the refinement
difference `𝔼(f|Q) - 𝔼(f|P)`. -/
lemma sum_compl_sub_mul_eq {P Q : X → Finset X} (hPmem : ∀ x, x ∈ P x)
    (hPeq : ∀ x y : X, y ∈ P x → P y = P x) (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) (href : ∀ x, Q x ⊆ P x)
    {Ω : Finset X} (hΩ : Sat Q Ω) (f h : X → ℝ) (hh : IsMeas Q h) :
    ∑ x ∈ Finset.univ \ Ω, (f x - cE P f x) * h x
      = ∑ x ∈ Finset.univ \ Ω, (cE Q f x - cE P f x) * h x := by
  rw [sum_sdiff_univ (Ω := Ω) (fun x => (f x - cE P f x) * h x),
    sum_sdiff_univ (Ω := Ω) (fun x => (cE Q f x - cE P f x) * h x)]
  set g : X → ℝ := fun x => (if x ∈ Ω then (0 : ℝ) else 1) * h x with hg
  have hgm : IsMeas Q g := isMeas_mul (isMeas_ind_compl hQmem hQeq hΩ) hh
  have hself : ∑ x, cE Q f x * g x = ∑ x, f x * g x :=
    sum_cE_mul_measurable hQmem hQeq f g hgm
  have e1 : ∀ x : X, (if x ∈ Ω then (0 : ℝ) else 1) * ((f x - cE P f x) * h x)
      = (f x - cE P f x) * g x := by intro x; simp only [hg]; ring
  have e2 : ∀ x : X, (if x ∈ Ω then (0 : ℝ) else 1) * ((cE Q f x - cE P f x) * h x)
      = (cE Q f x - cE P f x) * g x := by intro x; simp only [hg]; ring
  simp only [e1, e2]
  calc ∑ x, (f x - cE P f x) * g x
      = ∑ x, f x * g x - ∑ x, cE P f x * g x := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ = ∑ x, cE Q f x * g x - ∑ x, cE P f x * g x := by rw [hself]
    _ = ∑ x, (cE Q f x - cE P f x) * g x := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring

/-- **The cross-term identity of the Furstenberg tower step.**
Outside `Ω'`, the pairing of `𝔼(f|P)` with the refinement difference equals minus the
same pairing over the annulus `Ω' \ Ω`. -/
lemma sum_compl_cE_mul_sub {P Q : X → Finset X} (hPmem : ∀ x, x ∈ P x)
    (hPeq : ∀ x y : X, y ∈ P x → P y = P x) (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) (href : ∀ x, Q x ⊆ P x)
    {Ω Ω' : Finset X} (hΩsub : Ω ⊆ Ω') (hΩ : Sat P Ω) (hΩ' : Sat Q Ω') (f : X → ℝ) :
    ∑ x ∈ Finset.univ \ Ω', cE P f x * (cE Q f x - cE P f x)
      = - ∑ x ∈ Ω' \ Ω, cE P f x * (cE Q f x - cE P f x) := by
  rw [sum_sdiff_univ (Ω := Ω') (fun x => cE P f x * (cE Q f x - cE P f x))]
  have h0 := sum_ind_compl_mul_cE_sub hPmem hPeq hQmem hQeq href hΩ f
  have hsplit : ∀ x : X,
      (if x ∈ Ω' then (0 : ℝ) else 1) * (cE P f x * (cE Q f x - cE P f x))
        = (if x ∈ Ω then (0 : ℝ) else 1) * (cE P f x * (cE Q f x - cE P f x))
          + ((if x ∈ Ω' then (0 : ℝ) else 1) - (if x ∈ Ω then (0 : ℝ) else 1))
              * (cE P f x * (cE Q f x - cE P f x)) := by
    intro x; ring
  simp only [hsplit, Finset.sum_add_distrib, h0, zero_add]
  exact sum_ind_diff_eq hΩsub (fun x => cE P f x * (cE Q f x - cE P f x))

/-- **Self-adjointness of the annulus weight against the difference.** -/
lemma sum_annulus_cE_mul_sub {P Q : X → Finset X} (hPmem : ∀ x, x ∈ P x)
    (hPeq : ∀ x y : X, y ∈ P x → P y = P x) (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) (href : ∀ x, Q x ⊆ P x)
    {Ω Ω' : Finset X} (hΩsub : Ω ⊆ Ω') (hΩ : Sat P Ω) (hΩ' : Sat Q Ω') (f : X → ℝ) :
    ∑ x ∈ Ω' \ Ω, cE P f x * (cE Q f x - cE P f x)
      = ∑ x ∈ Ω' \ Ω, cE P f x * (f x - cE P f x) := by
  have hAQ : IsMeas Q (cE P f) := fun x y hy => cE_measurable hPeq f x y (href x hy)
  have hsat : Sat Q (Ω' \ Ω) :=
    Sat.sdiff hQeq hQmem (Sat.of_refines href hΩ) hΩ'
  set w : X → ℝ := fun x => (if x ∈ Ω' \ Ω then (1 : ℝ) else 0) * cE P f x with hw
  have hwQ : IsMeas Q w := isMeas_mul (isMeas_ind hQmem hQeq hsat) hAQ
  have key : ∀ u : X → ℝ, ∑ x ∈ Ω' \ Ω, cE P f x * u x = ∑ x, w x * u x := by
    intro u
    rw [← sum_indicator_eq (fun x => cE P f x * u x)]
    exact Finset.sum_congr rfl fun x _ => by simp only [hw]; ring
  rw [key (fun x => cE Q f x - cE P f x), key (fun x => f x - cE P f x)]
  have hsa' : ∑ x, cE Q f x * w x = ∑ x, f x * w x := sum_cE_mul_measurable hQmem hQeq f w hwQ
  have hsa : ∑ x, w x * cE Q f x = ∑ x, w x * f x := by
    rw [Finset.sum_congr rfl (fun x _ => by ring : ∀ x ∈ Finset.univ, w x * cE Q f x = cE Q f x * w x),
      Finset.sum_congr rfl (fun x _ => by ring : ∀ x ∈ Finset.univ, w x * f x = f x * w x), hsa']
  have e1 : ∀ x : X, w x * (cE Q f x - cE P f x) = w x * cE Q f x - w x * cE P f x :=
    fun x => by ring
  have e2 : ∀ x : X, w x * (f x - cE P f x) = w x * f x - w x * cE P f x :=
    fun x => by ring
  simp only [e1, e2, Finset.sum_sub_distrib, hsa]

/-- **Pythagoras with exceptional sets.** -/
lemma sum_sq_exceptional {P Q : X → Finset X} (hPmem : ∀ x, x ∈ P x)
    (hPeq : ∀ x y : X, y ∈ P x → P y = P x) (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) (href : ∀ x, Q x ⊆ P x)
    {Ω Ω' : Finset X} (hΩsub : Ω ⊆ Ω') (hΩ : Sat P Ω) (hΩ' : Sat Q Ω') (f : X → ℝ) :
    ∑ x ∈ Finset.univ \ Ω', (cE Q f x) ^ 2
      = ∑ x ∈ Finset.univ \ Ω', (cE P f x) ^ 2
        + ∑ x ∈ Finset.univ \ Ω', (cE Q f x - cE P f x) ^ 2
        - 2 * ∑ x ∈ Ω' \ Ω, cE P f x * (cE Q f x - cE P f x) := by
  have hpoint : ∀ x : X, (if x ∈ Ω' then (0 : ℝ) else 1) * (cE Q f x) ^ 2
      = (if x ∈ Ω' then (0 : ℝ) else 1) * (cE P f x) ^ 2
        + (if x ∈ Ω' then (0 : ℝ) else 1) * (cE Q f x - cE P f x) ^ 2
        + 2 * ((if x ∈ Ω' then (0 : ℝ) else 1) * (cE P f x * (cE Q f x - cE P f x))) := by
    intro x; ring
  rw [sum_sdiff_univ (Ω := Ω') (fun x => (cE Q f x) ^ 2),
    sum_sdiff_univ (Ω := Ω') (fun x => (cE P f x) ^ 2),
    sum_sdiff_univ (Ω := Ω') (fun x => (cE Q f x - cE P f x) ^ 2)]
  have hcross : ∑ x, (if x ∈ Ω' then (0 : ℝ) else 1) * (cE P f x * (cE Q f x - cE P f x))
      = - ∑ x ∈ Ω' \ Ω, cE P f x * (cE Q f x - cE P f x) := by
    rw [← sum_sdiff_univ (Ω := Ω') (fun x => cE P f x * (cE Q f x - cE P f x))]
    exact sum_compl_cE_mul_sub hPmem hPeq hQmem hQeq href hΩsub hΩ hΩ' f
  have hsum : ∑ x, (if x ∈ Ω' then (0 : ℝ) else 1) * (cE Q f x) ^ 2
      = ∑ x, (if x ∈ Ω' then (0 : ℝ) else 1) * (cE P f x) ^ 2
        + ∑ x, (if x ∈ Ω' then (0 : ℝ) else 1) * (cE Q f x - cE P f x) ^ 2
        + 2 * ∑ x, (if x ∈ Ω' then (0 : ℝ) else 1) * (cE P f x * (cE Q f x - cE P f x)) := by
    rw [show (∑ x, (if x ∈ Ω' then (0 : ℝ) else 1) * (cE Q f x) ^ 2)
        = ∑ x, ((if x ∈ Ω' then (0 : ℝ) else 1) * (cE P f x) ^ 2
            + (if x ∈ Ω' then (0 : ℝ) else 1) * (cE Q f x - cE P f x) ^ 2
            + 2 * ((if x ∈ Ω' then (0 : ℝ) else 1)
                * (cE P f x * (cE Q f x - cE P f x)))) from
          Finset.sum_congr rfl fun x _ => hpoint x]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    exact (Finset.mul_sum (s := Finset.univ) (a := 2)
      (f := fun x => (if x ∈ Ω' then (0 : ℝ) else 1)
        * (cE P f x * (cE Q f x - cE P f x)))).symm
  rw [hsum, hcross]
  ring

/-- Cauchy–Schwarz: a lower bound for a weighted pairing gives a lower bound for the
weighted `L²` norm. -/
lemma sq_div_le_sum_sq_of_corr [Nonempty X] {S : Finset X} {f h : X → ℝ} {M γ : ℝ}
    (hM : 0 < M) (hγ0 : 0 ≤ γ) (hh : ∀ x, |h x| ≤ M)
    (hγ : γ ≤ |∑ x ∈ S, f x * h x|) :
    γ ^ 2 / ((Fintype.card X : ℝ) * M ^ 2) ≤ ∑ x ∈ S, (f x) ^ 2 := by
  have hcard : 0 < Fintype.card X := Fintype.card_pos_iff.mpr (inferInstance : Nonempty X)
  have hNpos : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast hcard
  have hden : 0 < (Fintype.card X : ℝ) * M ^ 2 := by positivity
  have hcs : (∑ x ∈ S, f x * h x) ^ 2 ≤ (∑ x ∈ S, (f x) ^ 2) * ∑ x ∈ S, (h x) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq S f h
  have hh2 : ∑ x ∈ S, (h x) ^ 2 ≤ (Fintype.card X : ℝ) * M ^ 2 := by
    calc ∑ x ∈ S, (h x) ^ 2 ≤ ∑ _x ∈ S, M ^ 2 := by
          apply Finset.sum_le_sum; intro x _
          exact sq_le_sq.mpr (by rw [abs_of_nonneg hM.le]; exact hh x)
      _ = (S.card : ℝ) * M ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card X : ℝ) * M ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Finset.card_le_univ S
  have h1 : γ ^ 2 ≤ (∑ x ∈ S, f x * h x) ^ 2 :=
    sq_le_sq.mpr (by rw [abs_of_nonneg hγ0]; exact hγ)
  have hsq : γ ^ 2 ≤ (∑ x ∈ S, (f x) ^ 2) * ((Fintype.card X : ℝ) * M ^ 2) :=
    le_trans h1 (le_trans hcs (mul_le_mul_of_nonneg_left hh2
      (Finset.sum_nonneg fun x _ => sq_nonneg _)))
  rw [div_le_iff₀ hden]
  linarith

/-- **Energy increment with exceptional sets** (the Furstenberg tower step of
Green–Tao Proposition 7.2). -/
theorem energy_increment_exceptional [Nonempty X] {P Q : X → Finset X} (hPmem : ∀ x, x ∈ P x)
    (hPeq : ∀ x y : X, y ∈ P x → P y = P x) (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) (href : ∀ x, Q x ⊆ P x)
    {Ω Ω' : Finset X} (hΩsub : Ω ⊆ Ω') (hΩ : Sat P Ω) (hΩ' : Sat Q Ω')
    (f h : X → ℝ) (hh : IsMeas Q h) {B M γ E : ℝ} (hM : 0 < M) (hγ0 : 0 ≤ γ)
    (hA : ∀ x, x ∉ Ω → |cE P f x| ≤ B)
    (hhM : ∀ x, |h x| ≤ M)
    (hγ : γ ≤ |∑ x ∈ Finset.univ \ Ω', (f x - cE P f x) * h x|)
    (hE : ∑ x ∈ Ω' \ Ω, |f x - cE P f x| ≤ E) (hB0 : 0 ≤ B) :
    ∑ x ∈ Finset.univ \ Ω, (cE P f x) ^ 2 + γ ^ 2 / ((Fintype.card X : ℝ) * M ^ 2)
      ≤ ∑ x ∈ Finset.univ \ Ω', (cE Q f x) ^ 2
        + B ^ 2 * ((Ω' \ Ω).card : ℝ) + 2 * B * E := by
  classical
  have hred := sum_compl_sub_mul_eq hPmem hPeq hQmem hQeq href hΩ' f h hh
  have hγ' : γ ≤ |∑ x ∈ Finset.univ \ Ω', (cE Q f x - cE P f x) * h x| := by
    rw [← hred]; exact hγ
  have hcs := sq_div_le_sum_sq_of_corr (S := Finset.univ \ Ω')
    (f := fun x => cE Q f x - cE P f x) (h := h) hM hγ0 hhM hγ'
  have hpy := sum_sq_exceptional hPmem hPeq hQmem hQeq href hΩsub hΩ hΩ' f
  have hcross := sum_annulus_cE_mul_sub hPmem hPeq hQmem hQeq href hΩsub hΩ hΩ' f
  have hcross' : ∑ x ∈ Ω' \ Ω, cE P f x * (cE Q f x - cE P f x) ≤ B * E := by
    rw [hcross]
    calc ∑ x ∈ Ω' \ Ω, cE P f x * (f x - cE P f x)
        ≤ ∑ x ∈ Ω' \ Ω, B * |f x - cE P f x| := by
          apply Finset.sum_le_sum; intro x hx
          have hxΩ : x ∉ Ω := (Finset.mem_sdiff.mp hx).2
          have h1 : cE P f x * (f x - cE P f x) ≤ |cE P f x| * |f x - cE P f x| := by
            rw [← abs_mul]; exact le_abs_self _
          exact le_trans h1 (mul_le_mul_of_nonneg_right (hA x hxΩ) (abs_nonneg _))
      _ = B * ∑ x ∈ Ω' \ Ω, |f x - cE P f x| := by rw [Finset.mul_sum]
      _ ≤ B * E := mul_le_mul_of_nonneg_left hE hB0
  have hA2 : ∑ x ∈ Ω' \ Ω, (cE P f x) ^ 2 ≤ B ^ 2 * ((Ω' \ Ω).card : ℝ) := by
    calc ∑ x ∈ Ω' \ Ω, (cE P f x) ^ 2 ≤ ∑ _x ∈ Ω' \ Ω, B ^ 2 := by
          apply Finset.sum_le_sum; intro x hx
          have hxΩ : x ∉ Ω := (Finset.mem_sdiff.mp hx).2
          exact sq_le_sq.mpr (by rw [abs_of_nonneg hB0]; exact hA x hxΩ)
      _ = ((Ω' \ Ω).card : ℝ) * B ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = B ^ 2 * ((Ω' \ Ω).card : ℝ) := by ring
  have hsplitA : ∑ x ∈ Finset.univ \ Ω, (cE P f x) ^ 2
      = ∑ x ∈ Finset.univ \ Ω', (cE P f x) ^ 2 + ∑ x ∈ Ω' \ Ω, (cE P f x) ^ 2 := by
    have h1 := Finset.sum_sdiff (s₁ := Ω') (s₂ := Finset.univ)
      (f := fun x => (cE P f x) ^ 2) (Finset.subset_univ Ω')
    have h2 := Finset.sum_sdiff (s₁ := Ω) (s₂ := Finset.univ)
      (f := fun x => (cE P f x) ^ 2) (Finset.subset_univ Ω)
    have h3 := Finset.sum_sdiff (s₁ := Ω) (s₂ := Ω')
      (f := fun x => (cE P f x) ^ 2) hΩsub
    linarith [h1, h2, h3]
  linarith [hcs, hpy, hcross', hA2, hsplitA]

end FinSigma
