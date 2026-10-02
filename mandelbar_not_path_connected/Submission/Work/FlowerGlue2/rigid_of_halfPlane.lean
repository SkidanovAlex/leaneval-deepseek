import Mathlib
import Submission.Work.FlowerGlue.cyl_rigid

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

open Complex Filter
open scoped Real Topology

noncomputable section

/-- Backwards iterates of the shift relation: if `T (w+1) = T w + 1` on the half-plane
`Re w < -R`, then `T (w - n) = T w - n` for every natural `n` and every `w` in that half-plane. -/
lemma hper_sub_nat {R : ℝ} {T : ℂ → ℂ}
    (hper : ∀ w : ℂ, w.re < -R → T (w + 1) = T w + 1)
    {w : ℂ} (hw : w.re < -R) (n : ℕ) :
    T (w - (n : ℂ)) = T w - (n : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hu : (w - (n : ℂ)).re < -R := by
      rw [Complex.sub_re]; norm_cast
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hstep : T ((w - (n:ℂ)) - 1) = T (w - (n:ℂ)) - 1 := by
      have h := hper ((w - (n:ℂ)) - 1) (by
        rw [Complex.sub_re]; norm_cast; linarith)
      rw [sub_add_cancel] at h
      rw [h]; ring
    have hcast : w - ((n + 1 : ℕ) : ℂ) = (w - (n:ℂ)) - 1 := by
      rw [Nat.cast_succ]; ring
    rw [hcast, hstep, ih]
    push_cast; ring

/-- The quantity `T (ζ - k) + k` is independent of the integer `k`, as long as
`Re (ζ - k) < -R`. This is what makes the extension to the whole plane well defined. -/
lemma translate_indep {R : ℝ} {T : ℂ → ℂ}
    (hper : ∀ w : ℂ, w.re < -R → T (w + 1) = T w + 1)
    {ζ : ℂ} {k k' : ℤ} (hk : (ζ - (k : ℂ)).re < -R) (hk' : (ζ - (k' : ℂ)).re < -R) :
    T (ζ - (k : ℂ)) + (k : ℂ) = T (ζ - (k' : ℂ)) + (k' : ℂ) := by
  have key : ∀ (a b : ℤ), a ≤ b → (ζ - (a : ℂ)).re < -R → (ζ - (b : ℂ)).re < -R →
      T (ζ - (a : ℂ)) + (a : ℂ) = T (ζ - (b : ℂ)) + (b : ℂ) := by
    intro a b hab ha _
    obtain ⟨m, hm⟩ := Int.le.dest hab
    rw [← hm]
    have hcast : ζ - ((a + (m:ℤ) : ℤ) : ℂ) = (ζ - (a : ℂ)) - ((m:ℕ) : ℂ) := by
      push_cast; ring
    rw [hcast, hper_sub_nat hper ha m]
    push_cast; ring
  rcases le_total k k' with h | h
  · exact key k k' h hk hk'
  · exact (key k' k h hk' hk).symm

/-- A holomorphic, injective, shift-equivariant map defined on a left half-plane is the
restriction of a translation: there is `s` with `T w = w + s` for all `w` with `Re w < -R`.
(Extend `T` to an entire injective equivariant map by `T̃ ζ = T (ζ - k) + k` for an integer
`k` with `Re (ζ - k) < -R`, then apply `Work.FlowerGlue.cyl_rigid`.) -/
theorem rigid_of_halfPlane {R : ℝ} {T : ℂ → ℂ}
    (hd : DifferentiableOn ℂ T {w : ℂ | w.re < -R})
    (hinj : Set.InjOn T {w : ℂ | w.re < -R})
    (hper : ∀ w : ℂ, w.re < -R → T (w + 1) = T w + 1) :
    ∃ s : ℂ, ∀ w : ℂ, w.re < -R → T w = w + s := by
  classical
  -- a choice of integer shift taking `ζ` into the half-plane
  let K : ℂ → ℤ := fun ζ => Classical.choose (exists_int_gt (ζ.re + R))
  have hK : ∀ ζ : ℂ, ζ.re + R < (K ζ : ℝ) :=
    fun ζ => Classical.choose_spec (exists_int_gt (ζ.re + R))
  have hKdom : ∀ ζ : ℂ, (ζ - ((K ζ : ℤ) : ℂ)).re < -R := fun ζ => by
    have h := hK ζ
    rw [Complex.sub_re]; norm_cast; linarith
  -- the entire extension
  let Tt : ℂ → ℂ := fun ζ => T (ζ - ((K ζ : ℤ) : ℂ)) + ((K ζ : ℤ) : ℂ)
  have hval : ∀ ζ (k : ℤ), (ζ - (k : ℂ)).re < -R →
      T (ζ - (k : ℂ)) + (k : ℂ) = Tt ζ := by
    intro ζ k hk
    change T (ζ - (k : ℂ)) + (k : ℂ) = T (ζ - ((K ζ : ℤ) : ℂ)) + ((K ζ : ℤ) : ℂ)
    exact translate_indep hper hk (hKdom ζ)
  -- `Tt` is differentiable everywhere
  have hTtdiff : Differentiable ℂ Tt := by
    intro ζ₀
    have hζ₀ : (ζ₀ - ((K ζ₀ : ℤ) : ℂ)).re < -R := hKdom ζ₀
    have hopen : IsOpen {w : ℂ | w.re < -R} :=
      isOpen_lt Complex.continuous_re continuous_const
    have h2 : DifferentiableAt ℂ T (ζ₀ - ((K ζ₀ : ℤ) : ℂ)) :=
      hd.differentiableAt (hopen.mem_nhds hζ₀)
    have h1 : DifferentiableAt ℂ (fun ζ : ℂ => ζ - ((K ζ₀ : ℤ) : ℂ)) ζ₀ :=
      differentiableAt_id.sub_const _
    have hcomp : DifferentiableAt ℂ (T ∘ fun ζ : ℂ => ζ - ((K ζ₀ : ℤ) : ℂ)) ζ₀ :=
      h2.comp ζ₀ h1
    have hdiff : DifferentiableAt ℂ
        (fun ζ => T (ζ - ((K ζ₀ : ℤ) : ℂ)) + ((K ζ₀ : ℤ) : ℂ)) ζ₀ :=
      hcomp.add_const _
    have hVopen : IsOpen {ζ : ℂ | (ζ - ((K ζ₀ : ℤ) : ℂ)).re < -R} := by
      have heq : {ζ : ℂ | (ζ - ((K ζ₀ : ℤ) : ℂ)).re < -R}
          = {ζ : ℂ | ζ.re < -R + ((K ζ₀ : ℤ) : ℝ)} := by
        ext ζ
        rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Complex.sub_re]
        norm_cast
        constructor <;> intro h <;> linarith
      rw [heq]
      exact isOpen_lt Complex.continuous_re continuous_const
    have hev : Tt =ᶠ[nhds ζ₀]
        (fun ζ => T (ζ - ((K ζ₀ : ℤ) : ℂ)) + ((K ζ₀ : ℤ) : ℂ)) := by
      filter_upwards [hVopen.mem_nhds hζ₀] with ζ hζ
      exact (hval ζ (K ζ₀) hζ).symm
    exact hdiff.congr_of_eventuallyEq hev
  -- `Tt` is injective
  have hTtinj : Function.Injective Tt := by
    intro a b hab
    set k : ℤ := max (K a) (K b) with hk
    have hka : (a - (k : ℂ)).re < -R := by
      have h := hK a
      have hle : (K a : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_max_left (K a) (K b)
      rw [Complex.sub_re]; norm_cast; linarith
    have hkb : (b - (k : ℂ)).re < -R := by
      have h := hK b
      have hle : (K b : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_max_right (K a) (K b)
      rw [Complex.sub_re]; norm_cast; linarith
    have ha := hval a k hka
    have hb := hval b k hkb
    rw [← ha, ← hb] at hab
    have hTeq : T (a - (k : ℂ)) = T (b - (k : ℂ)) := add_right_cancel hab
    have hin : a - (k : ℂ) = b - (k : ℂ) := hinj hka hkb hTeq
    exact sub_left_inj.mp hin
  -- `Tt` is shift-equivariant
  have hTtper : ∀ ζ : ℂ, Tt (ζ + 1) = Tt ζ + 1 := by
    intro ζ
    set k : ℤ := K (ζ + 1) with hk
    have hkd : ((ζ + 1) - (k : ℂ)).re < -R := hKdom (ζ + 1)
    have hkd' : (ζ - (k : ℂ)).re < -R := by
      rw [Complex.sub_re] at hkd ⊢
      norm_cast at hkd ⊢
      have : (ζ + 1).re = ζ.re + 1 := by simp
      linarith
    have ha := hval (ζ + 1) k hkd
    have hb := hval ζ k hkd'
    rw [← ha, ← hb]
    have harg : ζ + 1 - (k : ℂ) = (ζ - (k : ℂ)) + 1 := by ring
    rw [harg, hper (ζ - (k : ℂ)) hkd']
    ring
  -- conclude
  obtain ⟨s, hs⟩ := Work.FlowerGlue.cyl_rigid hTtdiff hTtinj hTtper
  refine ⟨s, fun w hw => ?_⟩
  have hw0 : (w - ((0:ℤ):ℂ)).re < -R := by simpa using hw
  have hTw : T w = Tt w := by simpa using hval w 0 hw0
  rw [hTw]
  exact hs w

end

end Work.FlowerGlue2
