import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.gholo
import Submission.Work.Repel.invFunOn_differentiableOn

namespace Work.L62

open MandelDim Set Metric Filter Topology
open scoped Topology

noncomputable section

/-! ## Elementary facts about `Function.invFunOn`

`invFunOn f s` is the (classically chosen) inverse of `f` along `s`: for `y ∈ f '' s` it returns a
point of `s` mapping to `y`.  On the image it is a genuine inverse as soon as `f` is injective
on `s`. -/

/-- `invFunOn f s` is a left inverse of `f` on `s` when `f` is injective there. -/
theorem invFunOn_eq_self {f : ℂ → ℂ} {s : Set ℂ} (hinj : Set.InjOn f s) {x : ℂ} (hx : x ∈ s) :
    Function.invFunOn f s (f x) = x :=
  hinj (Function.invFunOn_mem ⟨x, hx, rfl⟩) hx (Function.invFunOn_eq ⟨x, hx, rfl⟩)

/-- The image of the inverse along the image of `f`. -/
theorem invFunOn_image {f : ℂ → ℂ} {s t : Set ℂ} (hinj : Set.InjOn f s) (h : f '' s = t) :
    Function.invFunOn f s '' t = s := by
  subst h
  ext y
  constructor
  · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩
    rw [invFunOn_eq_self hinj hx]
    exact hx
  · intro hy
    exact ⟨f y, ⟨y, hy, rfl⟩, invFunOn_eq_self hinj hy⟩

/-- The inverse along the image is injective. -/
theorem invFunOn_injOn {f : ℂ → ℂ} {s t : Set ℂ} (hinj : Set.InjOn f s) (h : f '' s = t) :
    Set.InjOn (Function.invFunOn f s) t := by
  intro a ha b hb hab
  have ha' : a ∈ f '' s := by rw [h]; exact ha
  have hb' : b ∈ f '' s := by rw [h]; exact hb
  rw [← Function.invFunOn_eq ha', ← Function.invFunOn_eq hb', hab]

/-- **One step of a chain of inverse branches.**  If `f` is holomorphic and injective on the open
set `U` with image `V`, then the inverse branch `invFunOn f U` is holomorphic and injective on `V`
with image exactly `U`. -/
theorem invFunOn_step {f : ℂ → ℂ} {U V : Set ℂ} (hUo : IsOpen U) (hinj : Set.InjOn f U)
    (hdiff : DifferentiableOn ℂ f U) (himg : f '' U = V) :
    DifferentiableOn ℂ (Function.invFunOn f U) V ∧ Set.InjOn (Function.invFunOn f U) V ∧
      Function.invFunOn f U '' V = U := by
  refine ⟨?_, invFunOn_injOn hinj himg, invFunOn_image hinj himg⟩
  have h := Work.Repel.invFunOn_differentiableOn (φ := f) (D := U) hUo hinj hdiff
  rwa [himg] at h

/-- The holomorphic branches of a model chain: given a chain of open connected sets `W j` with `W 0 = ball ζ₀ r` and `(d.E - β) '' W (j+1) = W j` injectively (`j < J`), and `W j ⊆ d.DE` (`1 ≤ j`), there are holomorphic parametrizations `Ψ j : ball ζ₀ r → W j` (`Ψ 0 = id`, injective on the ball, image `W j`) and holomorphic step inverses `ψ j : W j → W (j+1)` of `ĥ = d.E - β` compatible with `Ψ` (this is where `Work.Repel.invFunOn_differentiableOn` — the holomorphic inverse of an injective holomorphic function — is used). -/
theorem chain_branches {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ} {W : ℕ → Set ℂ} {J : ℕ} {ζ₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hW0 : W 0 = Metric.ball ζ₀ r)
    (hopen : ∀ j, j ≤ J → IsOpen (W j) ∧ IsConnected (W j))
    (hDE : ∀ j, 1 ≤ j → j ≤ J → W j ⊆ d.DE)
    (hchain : ∀ j, j < J → Set.InjOn (fun w => d.E w - β) (W (j + 1)) ∧
      (fun w => d.E w - β) '' W (j + 1) = W j) :
    ∃ (Ψ ψ : ℕ → ℂ → ℂ), (∀ z, Ψ 0 z = z) ∧
      (∀ j, j ≤ J → DifferentiableOn ℂ (Ψ j) (Metric.ball ζ₀ r) ∧
        Set.InjOn (Ψ j) (Metric.ball ζ₀ r) ∧ Ψ j '' Metric.ball ζ₀ r = W j) ∧
      (∀ j, j < J → DifferentiableOn ℂ (ψ j) (W j) ∧ Set.MapsTo (ψ j) (W j) (W (j + 1)) ∧
        (∀ w ∈ W j, (fun u => d.E u - β) (ψ j w) = w) ∧
        (∀ u ∈ Metric.ball ζ₀ r, ψ j (Ψ j u) = Ψ (j + 1) u)) := by
  classical
  -- the step map `ĥ = d.E - β` and the family of inverse branches of `ĥ` over the chain
  let F : ℂ → ℂ := fun w => d.E w - β
  let G : ℕ → ℂ → ℂ := fun j => Function.invFunOn F (W (j + 1))
  -- the iterated branch `Ψ j = G (j-1) ∘ ⋯ ∘ G 0`, `Ψ 0 = id`
  let Ψ : ℕ → ℂ → ℂ := Nat.rec (fun z : ℂ => z) (fun j f => G j ∘ f)
  have hF_eq : F = fun w => d.E w - β := rfl
  have hG_eq : ∀ j, G j = Function.invFunOn F (W (j + 1)) := fun _ => rfl
  have hΨ0 : Ψ 0 = fun z : ℂ => z := rfl
  have hΨsucc : ∀ n : ℕ, Ψ (n + 1) = G n ∘ Ψ n := fun _ => rfl
  -- `ĥ` is holomorphic on the domain `DE` of the lifted horn map
  have hFdiff : DifferentiableOn ℂ F d.DE := by
    have h := (Work.Horn.differentiableOn_E d).sub_const β
    simpa only [F] using h
  -- one step: the inverse branch over `W (n+1)` is holomorphic on `W n`, injective, image `W (n+1)`
  have key : ∀ n : ℕ, n < J → DifferentiableOn ℂ (G n) (W n) ∧ Set.InjOn (G n) (W n) ∧
      G n '' W n = W (n + 1) := by
    intro n hn
    have hnJ : n + 1 ≤ J := by omega
    have hsub : W (n + 1) ⊆ d.DE := hDE (n + 1) (by omega) hnJ
    have h := invFunOn_step (f := F) (U := W (n + 1)) (V := W n) (hopen (n + 1) hnJ).1
      (hchain n hn).1 (hFdiff.mono hsub) (hchain n hn).2
    simpa only [G] using h
  -- the branches `Ψ j`
  have P : ∀ j : ℕ, j ≤ J → DifferentiableOn ℂ (Ψ j) (Metric.ball ζ₀ r) ∧
      Set.InjOn (Ψ j) (Metric.ball ζ₀ r) ∧ Ψ j '' Metric.ball ζ₀ r = W j := by
    intro j
    induction j with
    | zero =>
        intro _
        refine ⟨?_, ?_, ?_⟩
        · rw [hΨ0]; exact differentiableOn_id
        · rw [hΨ0]; exact Set.injOn_id _
        · rw [hΨ0, hW0]; exact Set.image_id _
    | succ n ih =>
        intro hnJ
        have hk := key n (by omega)
        have ihn := ih (by omega)
        have hmap : Set.MapsTo (Ψ n) (Metric.ball ζ₀ r) (W n) := by
          intro z hz
          rw [← ihn.2.2]
          exact mem_image_of_mem _ hz
        have hcomp : DifferentiableOn ℂ (G n ∘ Ψ n) (Metric.ball ζ₀ r) :=
          hk.1.comp ihn.1 hmap
        have hinj : Set.InjOn (G n ∘ Ψ n) (Metric.ball ζ₀ r) :=
          hk.2.1.comp ihn.2.1 hmap
        have himg : (G n ∘ Ψ n) '' Metric.ball ζ₀ r = W (n + 1) := by
          rw [Set.image_comp (G n) (Ψ n), ihn.2.2, hk.2.2]
        rw [hΨsucc n]
        exact ⟨hcomp, hinj, himg⟩
  refine ⟨Ψ, G, ?_, P, ?_⟩
  · intro z; rw [hΨ0]
  · intro j hj
    obtain ⟨h1, h2, h3⟩ := key j hj
    have hmem : ∀ w ∈ W j, w ∈ F '' W (j + 1) := by
      intro w hw
      rw [hF_eq, (hchain j hj).2]
      exact hw
    refine ⟨h1, ?_, ?_, ?_⟩
    · intro w hw
      exact Function.invFunOn_mem (show ∃ a ∈ W (j + 1), F a = w from hmem w hw)
    · intro w hw
      exact Function.invFunOn_eq (show ∃ a ∈ W (j + 1), F a = w from hmem w hw)
    · intro u _
      rfl

end

end Work.L62
