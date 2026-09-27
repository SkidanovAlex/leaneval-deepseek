import Mathlib
import Submission.Work.Drive.PushDisc.milnorLens
import Submission.Work.Drive.PushDisc.thetaMapDefs
import Submission.Work.Drive.PushDisc.lensThetaAux

namespace Work.Drive.PushDisc

open scoped ContDiff

/-- **The rows of the framing map `θ`** (`Work.Drive.PushDisc.thetaMap`, `thetaMapDefs.lean`):

    θ (x,y,u,v) = Δ (x,y) + Σᵢ uᵢ • U (x,y) ᵢ + Σⱼ (r vⱼ) • W (x,y) ⱼ
                   + [ S₂ (x, r • v) - Δ (x, c x) - (fderiv ℝ (fun w => S₂ (x,w)) 0) (r • v) ].

The conclusion is the four rows the assembly consumes:

1. `θ` is `C^∞` on the whole model space (so that, by the compact-set globalisation
   `Work.Drive.PushDisc.exists_diffeo_of_localIsotopy_compact`, it can be turned into a global
   diffeo agreeing with it near the lens);
2. the **disc row** `θ (x,y,0,0) = Δ (x,y)` (the plane `{u = 0, v = 0}` is carried to the disc
   approximation) — from `S₂ (x,0) = Δ (x, c x)`, which is the top-edge row of `Δ`;
3. the **finger row** `θ (x, c x, 0, v) = S₂ (x, r • v)` — from `W (x, c x) = V x` and the row
   `(fderiv ℝ (fun w => S₂ (x,w)) 0) w = ∑ⱼ wⱼ • V x ⱼ` defining the `v`-frame `V` of the finger;
4. the **derivative row**: `fderiv ℝ θ (x,y,0,0) (a,b,u′,v′)
      = (fderiv ℝ Δ (x,y)) (a,b) + ∑ᵢ u′ᵢ • U (x,y) ᵢ + ∑ⱼ (r v′ⱼ) • W (x,y) ⱼ`
   (the bracket contributes nothing at `v = 0`: it vanishes identically there by row 2, its `v`-
   derivative is `r V x - r V x = 0`, and the `x,y`-derivatives vanish because the bracket is the
   zero function at `v = 0` for every `(x,y)`);
5. consequently `fderiv ℝ θ (x,y,0,0)` is **injective** on the lens as soon as the frame
   `[∂ₓΔ, ∂_yΔ, U, W]` is independent there and `r ≠ 0` (`0 < r`).

Both reviewers of the earlier version (without `hr`) correctly found that conjunct 5 fails at
`r = 0`; `hr` is now a hypothesis. -/
theorem lensThetaRows {k : ℕ}
    (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (U W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k)
    (V : ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (c : ℝ → ℝ) (r : ℝ) (hr : 0 < r)
    (hΔ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ)
    (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hS₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S₂)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (hS₂0 : ∀ x : ℝ, S₂ (x, 0) = Δ (x, c x))
    (hWc : ∀ x : ℝ, W (x, c x) = V x)
    (hV : ∀ (x : ℝ) (w : EuclideanSpace ℝ (Fin k)),
      (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (x, w)) 0) w = ∑ j : Fin k, w j • V x j)
    (hframe : ∀ p ∈ Work.Drive.PushDisc.lensK,
      LinearIndependent ℝ (Fin.append (Fin.append
        (Work.Drive.PushDisc.planeFrame k
          (fun q => fderiv ℝ Δ q (1, 0)) (fun q => fderiv ℝ Δ q (0, 1)) p) (U p)) (W p))) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Work.Drive.PushDisc.thetaMap Δ U W S₂ c r) ∧
      (∀ x y : ℝ, Work.Drive.PushDisc.thetaMap Δ U W S₂ c r (x, y, 0, 0) = Δ (x, y)) ∧
      (∀ (x : ℝ) (v : EuclideanSpace ℝ (Fin k)),
        Work.Drive.PushDisc.thetaMap Δ U W S₂ c r (x, c x, 0, v) = S₂ (x, r • v)) ∧
      (∀ (x y a b : ℝ) (u' v' : EuclideanSpace ℝ (Fin k)),
        fderiv ℝ (Work.Drive.PushDisc.thetaMap Δ U W S₂ c r) (x, y, 0, 0) (a, b, u', v')
          = (fderiv ℝ Δ (x, y)) (a, b)
            + (∑ i : Fin k, u' i • U (x, y) i)
            + (∑ j : Fin k, (r * v' j) • W (x, y) j)) ∧
      (∀ p ∈ Work.Drive.PushDisc.lensK,
        Function.Injective (fderiv ℝ (Work.Drive.PushDisc.thetaMap Δ U W S₂ c r) (p.1, p.2, 0, 0))) := by
  classical
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (thetaMap Δ U W S₂ c r) := by
    have hfun : thetaMap Δ U W S₂ c r = (fun ξ : Work.Drive.Whitney.Mdl k =>
        Δ (ξ.1, ξ.2.1) + (∑ i : Fin k, ξ.2.2.1 i • U (ξ.1, ξ.2.1) i)
          + (∑ j : Fin k, (r * ξ.2.2.2 j) • W (ξ.1, ξ.2.1) j)
          + (S₂ (ξ.1, r • ξ.2.2.2) - Δ (ξ.1, c ξ.1)
              - (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (ξ.1, w)) 0)
                  (r • ξ.2.2.2))) := by
      funext ξ
      rfl
    rw [hfun]
    fun_prop
  have hrow2 : ∀ x y : ℝ, thetaMap Δ U W S₂ c r (x, y, 0, 0) = Δ (x, y) := by
    intro x y
    simp only [thetaMap]
    show Δ (x, y) + (∑ i : Fin k, (0 : EuclideanSpace ℝ (Fin k)) i • U (x, y) i)
          + (∑ j : Fin k, (r * (0 : EuclideanSpace ℝ (Fin k)) j) • W (x, y) j)
          + (S₂ (x, r • (0 : EuclideanSpace ℝ (Fin k))) - Δ (x, c x)
              - (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (x, w)) 0)
                  (r • (0 : EuclideanSpace ℝ (Fin k)))) = Δ (x, y)
    have h1 : (∑ i : Fin k, (0 : EuclideanSpace ℝ (Fin k)) i • U (x, y) i) = 0 := by simp
    have h2 : (∑ j : Fin k, (r * (0 : EuclideanSpace ℝ (Fin k)) j) • W (x, y) j) = 0 := by simp
    have h3 : S₂ (x, r • (0 : EuclideanSpace ℝ (Fin k))) - Δ (x, c x)
        - (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (x, w)) 0)
            (r • (0 : EuclideanSpace ℝ (Fin k))) = 0 := by
      rw [smul_zero, map_zero, sub_zero, hS₂0 x, sub_self]
    rw [h1, h2, h3]
    simp
  have hrow3 : ∀ (x : ℝ) (v : EuclideanSpace ℝ (Fin k)),
      thetaMap Δ U W S₂ c r (x, c x, 0, v) = S₂ (x, r • v) := by
    intro x v
    simp only [thetaMap]
    show Δ (x, c x) + (∑ i : Fin k, (0 : EuclideanSpace ℝ (Fin k)) i • U (x, c x) i)
          + (∑ j : Fin k, (r * v j) • W (x, c x) j)
          + (S₂ (x, r • v) - Δ (x, c x)
              - (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (x, w)) 0) (r • v))
        = S₂ (x, r • v)
    have h1 : (∑ i : Fin k, (0 : EuclideanSpace ℝ (Fin k)) i • U (x, c x) i) = 0 := by simp
    have h2 : (∑ j : Fin k, (r * v j) • W (x, c x) j)
        = (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (x, w)) 0) (r • v) := by
      rw [hV x (r • v)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hWc x]
      congr 2
    rw [h1, h2]
    abel
  have hderiv : ∀ x y : ℝ,
      fderiv ℝ (thetaMap Δ U W S₂ c r) (x, y, 0, 0)
        = ((fderiv ℝ Δ (x, y)).comp piXY)
          + (∑ i : Fin k, (coU i).smulRight (U (x, y) i))
          + (∑ j : Fin k, (r • coV j).smulRight (W (x, y) j)) := by
    intro x y
    have hA := hasFDerivAt_delta Δ hΔ x y
    have hB := hasFDerivAt_usum U hU x y
    have hC := hasFDerivAt_vsum W hW r x y
    have hBr := hasFDerivAt_bracket Δ S₂ c hΔ hS₂ hc hS₂0 r x y
    have hsum := ((hA.add hB).add hC).add hBr
    have hfun : thetaMap Δ U W S₂ c r
        = ((fun ξ : Work.Drive.Whitney.Mdl k => Δ (ξ.1, ξ.2.1))
            + (fun ξ : Work.Drive.Whitney.Mdl k =>
                ∑ i : Fin k, ξ.2.2.1 i • U (ξ.1, ξ.2.1) i)
            + (fun ξ : Work.Drive.Whitney.Mdl k =>
                ∑ j : Fin k, (r * ξ.2.2.2 j) • W (ξ.1, ξ.2.1) j))
            + (fun ξ : Work.Drive.Whitney.Mdl k => S₂ (ξ.1, r • ξ.2.2.2) - Δ (ξ.1, c ξ.1)
                - (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (ξ.1, w)) 0)
                    (r • ξ.2.2.2)) := by
      funext ξ
      rfl
    have hsum' : HasFDerivAt (thetaMap Δ U W S₂ c r)
        ((((fderiv ℝ Δ (x, y)).comp piXY)
          + (∑ i : Fin k, (coU i).smulRight (U (x, y) i))
          + (∑ j : Fin k, (r • coV j).smulRight (W (x, y) j))) + 0)
        (x, y, 0, 0) := hfun.symm ▸ hsum
    rw [add_zero] at hsum'
    exact hsum'.fderiv
  have hderiv_apply : ∀ (x y : ℝ) (h : Work.Drive.Whitney.Mdl k),
      fderiv ℝ (thetaMap Δ U W S₂ c r) (x, y, 0, 0) h
        = (fderiv ℝ Δ (x, y)) (h.1, h.2.1)
          + (∑ i : Fin k, h.2.2.1 i • U (x, y) i)
          + (∑ j : Fin k, (r * h.2.2.2 j) • W (x, y) j) := by
    intro x y h
    rw [hderiv x y]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      sum_apply, smul_apply, piXY_apply, coU_apply, coV_apply, smul_eq_mul]
  refine ⟨hsm, hrow2, hrow3, ?_, ?_⟩
  · intro x y a b u' v'
    simpa using hderiv_apply x y (a, b, u', v')
  · intro p hp
    set L : Work.Drive.Whitney.Mdl k →L[ℝ] Work.Drive.Whitney.Mdl k :=
      ((fderiv ℝ Δ (p.1, p.2)).comp piXY)
        + (∑ i : Fin k, (coU i).smulRight (U (p.1, p.2) i))
        + (∑ j : Fin k, (r • coV j).smulRight (W (p.1, p.2) j)) with hLdef
    have hL : fderiv ℝ (thetaMap Δ U W S₂ c r) (p.1, p.2, 0, 0) = L := by
      rw [hderiv p.1 p.2, hLdef]
    rw [hL]
    have happ : ∀ h : Work.Drive.Whitney.Mdl k,
        L h = (fderiv ℝ Δ (p.1, p.2)) (h.1, h.2.1)
          + (∑ i : Fin k, h.2.2.1 i • U (p.1, p.2) i)
          + (∑ j : Fin k, (r * h.2.2.2 j) • W (p.1, p.2) j) := by
      intro h
      rw [← hL]
      exact hderiv_apply p.1 p.2 h
    set F : Fin (2 + k + k) → Work.Drive.Whitney.Mdl k :=
      Fin.append (Fin.append (planeFrame k (fun q => fderiv ℝ Δ q (1, 0))
        (fun q => fderiv ℝ Δ q (0, 1)) p) (U p)) (W p) with hFdef
    have hF : LinearIndependent ℝ F := hFdef.symm ▸ hframe p hp
    have hker : ∀ h : Work.Drive.Whitney.Mdl k, L h = 0 → h = 0 := by
      intro h hh
      rw [happ h] at hh
      set g : Fin (2 + k + k) → ℝ :=
        Fin.append (Fin.append (![h.1, h.2.1] : Fin 2 → ℝ) h.2.2.1) (fun j => r * h.2.2.2 j)
        with hgdef
      have hsum_eq : ∑ i : Fin (2 + k + k), g i • F i
          = (fderiv ℝ Δ (p.1, p.2)) (h.1, h.2.1)
            + (∑ i : Fin k, h.2.2.1 i • U (p.1, p.2) i)
            + (∑ j : Fin k, (r * h.2.2.2 j) • W (p.1, p.2) j) := by
        rw [hgdef, hFdef, sum_fin_append_smul, sum_fin_append_smul, Fin.sum_univ_two]
        simp only [planeFrame, Matrix.cons_val_zero, Matrix.cons_val_one]
        have hlin : h.1 • (fderiv ℝ Δ p (1, 0)) + h.2.1 • (fderiv ℝ Δ p (0, 1))
            = (fderiv ℝ Δ p) (h.1, h.2.1) := by
          have hp : (h.1, h.2.1) = h.1 • (1, 0) + h.2.1 • (0, 1) := by
            ext <;> simp
          rw [hp, map_add, map_smul, map_smul]
        rw [hlin]
      have hzero : ∑ i : Fin (2 + k + k), g i • F i = 0 := by
        rw [hsum_eq]; exact hh
      have hg : ∀ i, g i = 0 := (Fintype.linearIndependent_iff.mp hF) g hzero
      have hc1 : h.1 = 0 := by
        have h0 := hg (Fin.castAdd k (Fin.castAdd k (0 : Fin 2)))
        rwa [show g (Fin.castAdd k (Fin.castAdd k (0 : Fin 2))) = h.1 from by
          simp [hgdef, Fin.append_left]] at h0
      have hc2 : h.2.1 = 0 := by
        have h0 := hg (Fin.castAdd k (Fin.castAdd k (1 : Fin 2)))
        rwa [show g (Fin.castAdd k (Fin.castAdd k (1 : Fin 2))) = h.2.1 from by
          simp [hgdef, Fin.append_left]] at h0
      have hcu : h.2.2.1 = 0 := by
        ext i
        have h0 := hg (Fin.castAdd k (Fin.natAdd 2 i))
        rwa [show g (Fin.castAdd k (Fin.natAdd 2 i)) = h.2.2.1 i from by
          simp [hgdef, Fin.append_left, Fin.append_right]] at h0
      have hcv : h.2.2.2 = 0 := by
        ext j
        have h0 := hg (Fin.natAdd (2 + k) j)
        have h0' : g (Fin.natAdd (2 + k) j) = r * h.2.2.2 j := by
          simp [hgdef, Fin.append_right]
        rw [h0', mul_eq_zero] at h0
        exact h0.resolve_left (ne_of_gt hr)
      ext <;> simp_all
    intro h₁ h₂ hh
    have hsub : h₁ - h₂ = 0 := hker (h₁ - h₂) (by rw [map_sub, hh, sub_self])
    exact sub_eq_zero.mp hsub

end Work.Drive.PushDisc
