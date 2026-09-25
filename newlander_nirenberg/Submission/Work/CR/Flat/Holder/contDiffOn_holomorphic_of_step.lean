import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder

namespace Work.CR.Flat.Holder

noncomputable section

/-- The function obtained from `u` by applying the `(1,0)`-derivatives `dCoord`
along the list `l`, from right to left: `iterD u [] = u` and
`iterD u (j :: l) = dCoord j (iterD u l)`.  These are the elements of the
closure `S` of `{f}` under the maps `g ↦ fun z => dCoord j g z`, indexed by the
list of directions along which we differentiate. -/
noncomputable def iterD {n : ℕ} (u : (Fin n → ℂ) → ℂ) : List (Fin n) → ((Fin n → ℂ) → ℂ)
  | [] => u
  | j :: l => Work.CR.Flat.dCoord j (iterD u l)

@[simp] lemma iterD_nil {n : ℕ} (u : (Fin n → ℂ) → ℂ) : iterD u [] = u := rfl

@[simp] lemma iterD_cons {n : ℕ} (u : (Fin n → ℂ) → ℂ) (j : Fin n) (l : List (Fin n)) :
    iterD u (j :: l) = Work.CR.Flat.dCoord j (iterD u l) := rfl

/-- **A `C¹` holomorphic function is `C^N` for every `N`** — recursive form, given the two
ingredient lemmas as hypotheses so that it is independent of them.

`step` is the statement that `(1,0)`-derivatives of `C¹` holomorphic functions are again `C¹`
holomorphic; `upgrade` is the statement that a function which is differentiable, `C^m`, and whose
Wirtinger derivatives are `C^m` is `C^{m+1}`.

Proof: let `S` be the smallest set of functions `ℂⁿ → ℂ` containing `f` and closed under
`g ↦ fun z => dCoord j g z` (an inductive predicate), and prove by induction on `N : ℕ` the
statement `∀ g ∈ S, ContDiffOn ℝ N g Ω`. For `N = 1` every element of `S` is `C¹` and
holomorphic on `Ω` by induction on the derivation using `step`. The induction step from `N` to
`N + 1` uses `upgrade` with `h := g` and `m := N`: `g ∈ S` is `C^N` by the induction hypothesis,
`g` is differentiable (from `N ≥ 1`, or from the `C¹` statement when `N = 0`), each
`fun z => dCoord j g z` is `C^N` because it is again an element of `S`, and each
`fun z => dbarCoord j g z` is `C^N` because it is identically `0` (holomorphy). The conclusion
for `f` is the case `g = f` of the base element of `S`. -/
theorem contDiffOn_holomorphic_of_step {n : ℕ}
    (step : ∀ {Ω : Set (Fin n → ℂ)}, IsOpen Ω → ∀ {g : (Fin n → ℂ) → ℂ},
      ContDiffOn ℝ 1 g Ω → (∀ j, ∀ z ∈ Ω, Work.CR.Flat.dbarCoord j g z = 0) →
      ∀ j, ContDiffOn ℝ 1 (fun z => Work.CR.Flat.dCoord j g z) Ω ∧
        (∀ k, ∀ z ∈ Ω, Work.CR.Flat.dbarCoord k (Work.CR.Flat.dCoord j g) z = 0))
    (upgrade : ∀ {Ω : Set (Fin n → ℂ)}, IsOpen Ω → ∀ {h : (Fin n → ℂ) → ℂ} {m : ℕ},
      DifferentiableOn ℝ h Ω → ContDiffOn ℝ ((m : ℕ) : ℕ∞) h Ω →
      (∀ j, ContDiffOn ℝ ((m : ℕ) : ℕ∞) (fun z => Work.CR.Flat.dCoord j h z) Ω) →
      (∀ j, ContDiffOn ℝ ((m : ℕ) : ℕ∞) (fun z => Work.CR.Flat.dbarCoord j h z) Ω) →
      ContDiffOn ℝ (((m + 1 : ℕ)) : ℕ∞) h Ω)
    {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω) {f : (Fin n → ℂ) → ℂ} (hf : ContDiffOn ℝ 1 f Ω)
    (hhol : ∀ j, ∀ z ∈ Ω, Work.CR.Flat.dbarCoord j f z = 0) :
    ∀ N : ℕ, ContDiffOn ℝ ((N : ℕ) : ℕ∞) f Ω := by
  -- Every element of the closure `S` of `{f}` under `g ↦ fun z => dCoord j g z`
  -- (indexed by the list of differentiation directions) is `C¹` and holomorphic.
  have hbase : ∀ l : List (Fin n), ContDiffOn ℝ 1 (iterD f l) Ω ∧
      ∀ k, ∀ z ∈ Ω, Work.CR.Flat.dbarCoord k (iterD f l) z = 0 := by
    intro l
    induction l with
    | nil => exact ⟨by simpa using hf, by simpa using hhol⟩
    | cons j l ih =>
        obtain ⟨h1, h2⟩ := ih
        obtain ⟨s1, s2⟩ := step hΩ h1 h2 j
        exact ⟨by simpa [iterD] using s1, by simpa [iterD] using s2⟩
  -- Induction on the regularity order.
  have hmain : ∀ N : ℕ, ∀ l : List (Fin n), ContDiffOn ℝ (N : ℕ∞) (iterD f l) Ω := by
    intro N
    induction N with
    | zero =>
        intro l
        exact (hbase l).1.of_le (by norm_num)
    | succ N ih =>
        intro l
        -- `g` is differentiable, since it is `C¹` by `hbase`.
        have hdiff : DifferentiableOn ℝ (iterD f l) Ω :=
          (hbase l).1.differentiableOn (by norm_num)
        -- `g` is `C^N` by the induction hypothesis.
        have hN : ContDiffOn ℝ (N : ℕ∞) (iterD f l) Ω := ih l
        -- Its `(1,0)`-derivatives are `C^N`, being again in `S`.
        have hd : ∀ j, ContDiffOn ℝ (N : ℕ∞)
            (fun z => Work.CR.Flat.dCoord j (iterD f l) z) Ω := by
          intro j; simpa [iterD] using ih (j :: l)
        -- Its `(0,1)`-derivatives vanish on `Ω` by holomorphy.
        have hdb : ∀ j, ContDiffOn ℝ (N : ℕ∞)
            (fun z => Work.CR.Flat.dbarCoord j (iterD f l) z) Ω := by
          intro j
          exact (contDiffOn_const (c := (0 : ℂ))).congr
            (fun z hz => by rw [(hbase l).2 j z hz])
        have := upgrade hΩ hdiff hN hd hdb
        simpa [Nat.succ_eq_add_one] using this
  intro N
  simpa using hmain N []

end

end Work.CR.Flat.Holder
