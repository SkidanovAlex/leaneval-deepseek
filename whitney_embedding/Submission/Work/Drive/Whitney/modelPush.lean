import Mathlib

namespace Work.Drive.Whitney

/-!
# M1: the model move of the Whitney trick in coordinates

`ℝ^{2n}` is written as `ℝ × ℝ × E × E` with `E = EuclideanSpace ℝ (Fin k)`; a point is `(x,y,u,v)`.
The two model sheets are `A = {(x,0,u,0)}` and `B = {(x, c x, 0, v)}`, and `c` vanishes exactly at
`±1`, is positive on `(-1,1)`, and negative outside.

The move is the explicit vertical shear `ψ (x,y,u,v) = (x, y - 2 m x * l (‖v‖^2), u, v)` whose
inverse is `σ (x,y,u,v) = (x, y + 2 m x * l (‖v‖^2), u, v)`.  Because `ψ` changes only the
`y`-coordinate, no fold condition is needed and `σ` is the inverse on the nose.  (The amplitude is a
smooth function of `‖v‖^2` -- equivalently a radial function flat at `v = 0` -- so that smoothness
holds; `l (‖v‖)` would not be smooth at the origin.)  Everything here is pure calculus.

The last clause is the point of the model: `A` forces `v = 0`, and at `v = 0` the moved height is
`c x - 2 m x < 0` (the first conjunct), so a *moved* point of `B` is off `A`; and it is off `B` too,
because the shear is non-trivial there.  This is the "drop direction in which the partner branch is
absent".
-/

namespace Work.Drive.Whitney

open scoped ContDiff

/-- **M1: the model move.** -/
theorem modelPush {k : ℕ} (c m l : ℝ → ℝ)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m)
    (hl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) l)
    (hc1 : c 1 = 0) (hcneg1 : c (-1) = 0)
    (hcpos : ∀ x : ℝ, -1 < x → x < 1 → 0 < c x)
    (hcneg : ∀ x : ℝ, 1 < |x| → c x < 0)
    (hmbig : ∀ x : ℝ, |x| ≤ 1 → max 0 (c x) + 1 ≤ m x)
    (hmsmall : ∀ x : ℝ, 3 / 2 ≤ |x| → m x = 0)
    (hmnn : ∀ x : ℝ, 0 ≤ m x)
    (hl0 : l 0 = 1)
    (hlsmall : ∀ t : ℝ, 1 ≤ t → l t = 0)
    (hlnn : ∀ t : ℝ, 0 ≤ l t) :
    (∀ x : ℝ, c x - 2 * m x < 0) ∧
    (let E := EuclideanSpace ℝ (Fin k)
     let ψ : ℝ × ℝ × E × E → ℝ × ℝ × E × E :=
       fun z => (z.1, z.2.1 - 2 * m z.1 * l (‖z.2.2.2‖ ^ 2), z.2.2.1, z.2.2.2)
     let σ : ℝ × ℝ × E × E → ℝ × ℝ × E × E :=
       fun z => (z.1, z.2.1 + 2 * m z.1 * l (‖z.2.2.2‖ ^ 2), z.2.2.1, z.2.2.2)
     ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
     ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
     (∀ z, σ (ψ z) = z) ∧
     (∀ z, ψ (σ z) = z) ∧
     (∀ z, ψ z = z ↔ m z.1 * l (‖z.2.2.2‖ ^ 2) = 0) ∧
     (∀ x : ℝ, ∀ v : E, ψ (x, c x, 0, v) = (x, c x - 2 * m x * l (‖v‖ ^ 2), 0, v)) ∧
     (∀ x : ℝ, ∀ v : E, m x ≠ 0 → l (‖v‖ ^ 2) ≠ 0 →
        ψ (x, c x, 0, v) ∉ {z : ℝ × ℝ × E × E | z.2.1 = 0 ∧ z.2.2.2 = 0} ∧
        ψ (x, c x, 0, v) ∉ {z : ℝ × ℝ × E × E | z.2.2.1 = 0 ∧ z.2.1 = c z.1})) := by
  -- The first conjunct: the moved height is strictly negative.  On `|x| ≤ 1` we have `c x ≥ 0`
  -- and `m x ≥ max 0 (c x) + 1`, so `c x - 2 m x ≤ -c x - 2 < 0`; off `[-1,1]` we have `c x < 0`
  -- and `m x ≥ 0`, so `c x - 2 m x ≤ c x < 0`.
  have hdrop : ∀ x : ℝ, c x - 2 * m x < 0 := by
    intro x
    rcases le_or_gt (|x|) 1 with h | h
    · have hcxnn : 0 ≤ c x := by
        obtain ⟨hx1, hx2⟩ := abs_le.mp h
        by_cases hxm : x = -1
        · simp [hxm, hcneg1]
        by_cases hxp : x = 1
        · simp [hxp, hc1]
        · exact le_of_lt (hcpos x (lt_of_le_of_ne hx1 (Ne.symm hxm)) (lt_of_le_of_ne hx2 hxp))
      linarith [hmbig x h, le_max_right (0 : ℝ) (c x), hcxnn]
    · linarith [hcneg x h, hmnn x]
  -- Smoothness of `ψ` and `σ`: both are built from the projections of `ℝ × ℝ × E × E`, the
  -- smooth scalar functions `m`, `l` and the (smooth) function `z ↦ ‖z.2.2.2‖ ^ 2`.
  let Z := ℝ × ℝ × EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)
  have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Z => z.2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp contDiff_snd)
  have hnorm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Z => ‖z.2.2.2‖ ^ 2) :=
    ContDiff.norm_sq ℝ h4
  have hm1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Z => m z.1) :=
    hm.comp contDiff_fst
  have hl4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Z => l (‖z.2.2.2‖ ^ 2)) :=
    hl.comp hnorm
  have h2m : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Z => 2 * m z.1) :=
    (contDiff_const (c := (2 : ℝ))).mul hm1
  have hprod : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Z => 2 * m z.1 * l (‖z.2.2.2‖ ^ 2)) :=
    h2m.mul hl4
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Z => z.2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
  have h1' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Z => z.1) := contDiff_fst
  have h2' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Z => z.2.1 - 2 * m z.1 * l (‖z.2.2.2‖ ^ 2)) :=
    (contDiff_fst.comp contDiff_snd).sub hprod
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Z => (z.1, z.2.1 - 2 * m z.1 * l (‖z.2.2.2‖ ^ 2), z.2.2.1, z.2.2.2)) :=
    h1'.prodMk (h2'.prodMk (h3.prodMk h4))
  have h2'' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Z => z.2.1 + 2 * m z.1 * l (‖z.2.2.2‖ ^ 2)) :=
    (contDiff_fst.comp contDiff_snd).add hprod
  have hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Z => (z.1, z.2.1 + 2 * m z.1 * l (‖z.2.2.2‖ ^ 2), z.2.2.1, z.2.2.2)) :=
    h1'.prodMk (h2''.prodMk (h3.prodMk h4))
  refine ⟨hdrop, ?_⟩
  dsimp only
  refine ⟨hψ, hσ, ?_, ?_, ?_, ?_, ?_⟩
  · -- `σ ∘ ψ = id`
    intro z
    simp [sub_add_cancel]
  · -- `ψ ∘ σ = id`
    intro z
    simp [add_sub_cancel_right]
  · -- `ψ` fixes exactly the points where the amplitude vanishes
    intro z
    constructor
    · intro h
      have h2 : z.2.1 - 2 * m z.1 * l (‖z.2.2.2‖ ^ 2) = z.2.1 := by
        simpa using congrArg (fun w : Z => w.2.1) h
      have h3 : (2 * m z.1) * l (‖z.2.2.2‖ ^ 2) = 0 := by linarith
      nlinarith [h3]
    · intro h
      have hX : (2 * m z.1) * l (‖z.2.2.2‖ ^ 2) = 0 := by nlinarith [h]
      show (z.1, z.2.1 - (2 * m z.1) * l (‖z.2.2.2‖ ^ 2), z.2.2.1, z.2.2.2) =
        (z.1, z.2.1, z.2.2.1, z.2.2.2)
      rw [hX, sub_zero]
  · -- the explicit formula on the `B`-sheet
    intro x v
    rfl
  · -- a moved point of `B` lies neither on `A` (`v = 0` forces height `< 0`) nor on `B`
    intro x v hmx hlv
    constructor
    · rintro ⟨h1, h2⟩
      have h2' : v = 0 := h2
      have h1' : c x - 2 * m x * l (‖v‖ ^ 2) = 0 := h1
      rw [h2'] at h1'
      simp [hl0] at h1'
      linarith [hdrop x]
    · rintro ⟨h1, h2⟩
      have h2' : c x - 2 * m x * l (‖v‖ ^ 2) = c x := h2
      have h3 : (2 * m x) * l (‖v‖ ^ 2) = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h | h
      · exact hmx (by linarith)
      · exact hlv h

end Work.Drive.Whitney

/-- The model move of the Whitney trick, available under the module name `Work.Drive.Whitney.modelPush`
(the statement above is nested in the namespace `Work.Drive.Whitney` twice, so its bare name carries the
nesting twice; this is the plain alias under the module's own name). -/
alias modelPush := Work.Drive.Whitney.Work.Drive.Whitney.modelPush

end Work.Drive.Whitney
