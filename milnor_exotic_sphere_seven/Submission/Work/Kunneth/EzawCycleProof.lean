import Mathlib
import Submission.Work.Kunneth.EzawCycle
import Submission.Work.Kunneth.EzawBoundary
import Submission.Work.Kunneth.Em_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- Distribution of a `ℤ`-scalar over a difference in a `ℤ`-module (instance-robust version). -/
lemma smul_sub_mod {M : Type*} [AddCommGroup M] [Module ℤ M] (c : ℤ) (x y : M) :
    c • (x - y) = c • x - c • y :=
  map_sub (c • (1 : M →ₗ[ℤ] M)) x y

/-- Chain-map property of `phiSum`, in application form. -/
lemma phiSum_d (p q k : ℕ) (x : ↥((tMod p q).X (k + 1))) :
    (tMod (p + 1) q).d (k + 1) k ((phiSum p q).f (k + 1) x)
      = (phiSum p q).f k ((tMod p q).d (k + 1) k x) := by
  change (ModuleCat.Hom.hom ((tMod (p + 1) q).d (k + 1) k))
      ((ModuleCat.Hom.hom ((phiSum p q).f (k + 1))) x)
    = (ModuleCat.Hom.hom ((phiSum p q).f k))
      ((ModuleCat.Hom.hom ((tMod p q).d (k + 1) k)) x)
  exact Hom_comm_apply (phiSum p q) (k + 1) k x

/-- Chain-map property of `psiSum`, in application form. -/
lemma psiSum_d (p q k : ℕ) (x : ↥((tMod p q).X (k + 1))) :
    (tMod p (q + 1)).d (k + 1) k ((psiSum p q).f (k + 1) x)
      = (psiSum p q).f k ((tMod p q).d (k + 1) k x) := by
  change (ModuleCat.Hom.hom ((tMod p (q + 1)).d (k + 1) k))
      ((ModuleCat.Hom.hom ((psiSum p q).f (k + 1))) x)
    = (ModuleCat.Hom.hom ((psiSum p q).f k))
      ((ModuleCat.Hom.hom ((tMod p q).d (k + 1) k)) x)
  exact Hom_comm_apply (psiSum p q) (k + 1) k x

/-- The differential of `phiTsum`. -/
lemma d_phiTsum (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ)
    (hW : (tMod p q).d (p + q + 1) (p + q) (W p q) = dfc W p q) :
    (tMod (p + 1) q).d ((p + 1) + q) ((p + 1) + q - 1) (phiTsum W p q)
      = dcast (p + 1) q (congrArg (fun k => k - 1) (Nat.add_right_comm p 1 q).symm)
          ((phiSum p q).f (p + q) (dfc W p q)) := by
  rw [phiTsum, d_dcast]
  congr 1
  show (tMod (p + 1) q).d (p + q + 1) (p + q)
      ((phiSum p q).f (p + q + 1) (W p q)) = (phiSum p q).f (p + q) (dfc W p q)
  rw [phiSum_d p q (p + q) (W p q), hW]

/-- The differential of `psiTsum`. -/
lemma d_psiTsum (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ)
    (hW : (tMod p q).d (p + q + 1) (p + q) (W p q) = dfc W p q) :
    (tMod p (q + 1)).d (p + (q + 1)) (p + (q + 1) - 1) (psiTsum W p q)
      = (psiSum p q).f (p + q) (dfc W p q) := by
  rw [psiTsum]
  show (tMod p (q + 1)).d (p + q + 1) (p + q) ((psiSum p q).f (p + q + 1) (W p q))
      = (psiSum p q).f (p + q) (dfc W p q)
  rw [psiSum_d p q (p + q) (W p q), hW]

/-- The defect in the `(0,0)` case is a cycle. -/
theorem dfc_cycle_zz (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) :
    (tMod 0 0).d (0 + 0) (0 + 0 - 1) (dfc W 0 0) = 0 := by
  have h : dfc W 0 0 = 0 := by
    rw [dfc_eq_dfc2]
    exact Em_zero
  rw [h, HomologicalComplex.shape (tMod 0 0) (0 + 0) (0 + 0 - 1) (by simp [ComplexShape.down])]
  change (ModuleCat.Hom.hom (0 : (tMod 0 0).X (0 + 0) ⟶ (tMod 0 0).X (0 + 0 - 1)))
    (0 : ↥((tMod 0 0).X (0 + 0))) = 0
  exact map_zero _

/-- The cycle condition in the case `(0, q+1)`. -/
theorem dfc_cycle_zp (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (q : ℕ)
    (hW : ∀ p' q', p' + q' < 0 + (q + 1) →
      (tMod p' q').d (p' + q' + 1) (p' + q') (W p' q') = dfc W p' q') :
    (tMod 0 (q + 1)).d (0 + (q + 1)) (0 + (q + 1) - 1) (dfc W 0 (q + 1)) = 0 := by
  rw [show (tMod 0 (q + 1)).d (0 + (q + 1)) (0 + (q + 1) - 1) (dfc W 0 (q + 1))
      = (tMod 0 (q + 1)).d ((0 + q) + 1) (0 + q) (Em 0 (q + 1) - psiTsum W 0 q) from by
    rw [dfc_eq_dfc2]
    rw [show dfc2 W 0 (q + 1) = Em 0 (q + 1) - psiTsum W 0 q from rfl]
    rfl]
  rw [map_sub]
  have hb := ezaw_boundary_zp q (0 + q) rfl rfl
  have hE1 : EmS 0 (q + 1) ((0 + q) + 1) rfl = Em 0 (q + 1) := by
    rw [show EmS 0 (q + 1) ((0 + q) + 1) rfl = EmS 0 (q + 1) (0 + (q + 1)) rfl from rfl]
    exact EmS_self 0 (q + 1)
  rw [← hE1, hb]
  have hp : (tMod 0 (q + 1)).d ((0 + q) + 1) (0 + q) (psiTsum W 0 q)
      = (psiSum 0 q).f (0 + q) (dfc W 0 q) := by
    have hd : (tMod 0 (q + 1)).d ((0 + q) + 1) (0 + q) (psiTsum W 0 q)
        = (tMod 0 (q + 1)).d (0 + q + 1) (0 + q) ((psiSum 0 q).f (0 + q + 1) (W 0 q)) := by
      rw [psiTsum]
    rw [hd, psiSum_d 0 q (0 + q) (W 0 q), hW 0 q (by omega)]
  rw [hp, EmS_self, ← map_sub]
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    have h00 : dfc W 0 0 = Em 0 0 := by rw [dfc_eq_dfc2]; rfl
    rw [h00, sub_self]
    change (ModuleCat.Hom.hom ((psiSum 0 0).f (0 + 0))) (0 : ↥((tMod 0 0).X (0 + 0))) = 0
    exact map_zero _
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [show dfc W 0 (q' + 1) = Em 0 (q' + 1) - psiTsum W 0 q' from by
      rw [dfc_eq_dfc2]
      rfl]
    rw [show Em 0 (q' + 1) - (Em 0 (q' + 1) - psiTsum W 0 q') = psiTsum W 0 q' from by abel]
    rw [psiTsum]
    exact psiSum_comp_apply 0 q' (0 + (q' + 1)) (W 0 q')

/-- The cycle condition in the case `(p+1, 0)`.  The final step of the case `p > 0` (the
identification of `d (phiTsum W p' 0)` with `(phiSum p' 0).f (p'+0) (dfc W p' 0)`) is the only
gap; see `STATUS_ezaw.md`. -/
theorem dfc_cycle_pz (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p : ℕ)
    (hW : ∀ p' q', p' + q' < (p + 1) + 0 →
      (tMod p' q').d (p' + q' + 1) (p' + q') (W p' q') = dfc W p' q') :
    (tMod (p + 1) 0).d ((p + 1) + 0) ((p + 1) + 0 - 1) (dfc W (p + 1) 0) = 0 := by
  rw [show (tMod (p + 1) 0).d ((p + 1) + 0) ((p + 1) + 0 - 1) (dfc W (p + 1) 0)
      = (tMod (p + 1) 0).d ((p + 0) + 1) (p + 0) (Em (p + 1) 0 - phiTsum W p 0) from by
    rw [dfc_eq_dfc2]
    rw [show dfc2 W (p + 1) 0 = Em (p + 1) 0 - phiTsum W p 0 from rfl]
    rfl]
  rw [map_sub]
  have hb := ezaw_boundary_pz p (p + 0) rfl rfl
  have hE1 : EmS (p + 1) 0 ((p + 0) + 1) rfl = Em (p + 1) 0 := by
    rw [show EmS (p + 1) 0 ((p + 0) + 1) rfl = EmS (p + 1) 0 ((p + 1) + 0) rfl from rfl]
    exact EmS_self (p + 1) 0
  rw [← hE1, hb]
  have hp : (tMod (p + 1) 0).d ((p + 0) + 1) (p + 0) (phiTsum W p 0)
      = (phiSum p 0).f (p + 0) (dfc W p 0) := by
    -- The degree transport in `phiTsum` is along a proof of `p + 0 + 1 = (p + 1) + 0`, whose
    -- two sides are both definitionally `p + 1`; hence it is the identity.
    have hX : dcast (p + 1) 0 (Nat.add_right_comm p 1 0).symm
        ((phiSum p 0).f (p + 0 + 1) (W p 0)) = (phiSum p 0).f (p + 0 + 1) (W p 0) := by
      rw [Subsingleton.elim (Nat.add_right_comm p 1 0).symm (rfl : p + 0 + 1 = p + 0 + 1),
        dcast_rfl]
    rw [phiTsum, hX, phiSum_d p 0 (p + 0) (W p 0), hW p 0 (by omega)]
  rw [hp, EmS_self, ← map_sub]
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · subst hp0
    have h00 : dfc W 0 0 = Em 0 0 := by rw [dfc_eq_dfc2]; rfl
    rw [h00, sub_self]
    change (ModuleCat.Hom.hom ((phiSum 0 0).f (0 + 0))) (0 : ↥((tMod 0 0).X (0 + 0))) = 0
    exact map_zero _
  · obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [show dfc W (p' + 1) 0 = Em (p' + 1) 0 - phiTsum W p' 0 from by
      rw [dfc_eq_dfc2]
      rfl]
    rw [show Em (p' + 1) 0 - (Em (p' + 1) 0 - phiTsum W p' 0) = phiTsum W p' 0 from by abel]
    rw [phiTsum]
    rw [dcast_chainMap (p' + 1) 0 (p' + 2) 0 (phiSum (p' + 1) 0)
      (Nat.add_right_comm p' 1 0).symm]
    rw [phiSum_comp_apply p' 0 (p' + 0 + 1) (W p' 0)]
    rfl

end

end Work.Kunneth

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- Chain map applied to a degree transport, in application form. -/
lemma dcast_chainMap' (p q p' q' : ℕ) (f : tMod p q ⟶ tMod p' q') {n m : ℕ} (h : n = m)
    (x : ↥((tMod p q).X n)) :
    (f.f m) (dcast p q h x) = dcast p' q' h ((f.f n) x) := by
  change (ModuleCat.Hom.hom (f.f m)) (dcast p q h x)
    = dcast p' q' h ((ModuleCat.Hom.hom (f.f n)) x)
  exact dcast_chainMap p q p' q' f h x

/-- **The reduction of the cycle condition for the pair `(p+1,q+1)` to the two defects
`Em p (q+1) - dfc W p (q+1)` and `Em (p+1) q - dfc W (p+1) q`.** -/
lemma dfc_cycle_pp_red (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (p q : ℕ) (h₁ : p + (q + 1) = (p + 1) + q)
    (hW : ∀ p' q', p' + q' < (p + 1) + (q + 1) →
      (tMod p' q').d (p' + q' + 1) (p' + q') (W p' q') = dfc W p' q') :
    (tMod (p + 1) (q + 1)).d ((p + 1) + (q + 1)) ((p + 1) + (q + 1) - 1)
        (dfc W (p + 1) (q + 1))
      = dcast (p + 1) (q + 1) h₁
          ((phiSum p (q + 1)).f (p + (q + 1)) (Em p (q + 1) - dfc W p (q + 1)))
        + (-1 : ℤ) ^ (p + 1) •
            (psiSum (p + 1) q).f ((p + 1) + q) (Em (p + 1) q - dfc W (p + 1) q) := by
  have hEE : (phiSum p (q + 1)).f ((p + 1) + q) (EmS p (q + 1) ((p + 1) + q) h₁)
      = dcast (p + 1) (q + 1) h₁
          ((phiSum p (q + 1)).f (p + (q + 1)) (Em p (q + 1))) := by
    rw [← EmS_dcast p (q + 1) ((p + 1) + q) h₁ h₁]
    exact dcast_chainMap' p (q + 1) (p + 1) (q + 1) (phiSum p (q + 1)) h₁ (Em p (q + 1))
  have hES : EmS (p + 1) q ((p + 1) + q) rfl = Em (p + 1) q := by
    rw [show EmS (p + 1) q ((p + 1) + q) rfl = EmS (p + 1) q ((p + 1) + q) rfl from rfl]
    exact EmS_self (p + 1) q
  -- the `Em` term, from the boundary identity
  have hEm : (tMod (p + 1) (q + 1)).d (((p + 1) + q) + 1) ((p + 1) + q)
        (Em (p + 1) (q + 1))
      = (phiSum p (q + 1)).f ((p + 1) + q) (EmS p (q + 1) ((p + 1) + q) h₁)
        + (-1 : ℤ) ^ (p + 1) • (psiSum (p + 1) q).f ((p + 1) + q)
            (EmS (p + 1) q ((p + 1) + q) rfl) := by
    have hb := ezaw_boundary_pp p q ((p + 1) + q) rfl h₁ rfl
    rw [show EmS (p + 1) (q + 1) (((p + 1) + q) + 1) rfl = Em (p + 1) (q + 1) from by
      rw [show EmS (p + 1) (q + 1) (((p + 1) + q) + 1) rfl
          = EmS (p + 1) (q + 1) ((p + 1) + (q + 1)) rfl from rfl]
      exact EmS_self (p + 1) (q + 1)] at hb
    exact hb
  -- the `phiTsum` term
  have hphi : (tMod (p + 1) (q + 1)).d ((p + 1) + (q + 1)) ((p + 1) + (q + 1) - 1)
        (phiTsum W p (q + 1))
      = dcast (p + 1) (q + 1) h₁
          ((phiSum p (q + 1)).f (p + (q + 1)) (dfc W p (q + 1))) := by
    have hd1 := d_phiTsum W p (q + 1) (hW p (q + 1) (by omega))
    rw [hd1, Subsingleton.elim
      (congrArg (fun k => k - 1) (Nat.add_right_comm p 1 (q + 1)).symm) h₁]
  have hpsi : (tMod (p + 1) (q + 1)).d ((p + 1) + (q + 1)) ((p + 1) + (q + 1) - 1)
        (psiTsum W (p + 1) q)
      = (psiSum (p + 1) q).f ((p + 1) + q) (dfc W (p + 1) q) :=
    d_psiTsum W (p + 1) q (hW (p + 1) q (by omega))
  -- assemble
  have hexp : (tMod (p + 1) (q + 1)).d ((p + 1) + (q + 1)) ((p + 1) + (q + 1) - 1)
        (Em (p + 1) (q + 1) - phiTsum W p (q + 1)
          - (-1 : ℤ) ^ (p + 1) • psiTsum W (p + 1) q)
      = (phiSum p (q + 1)).f ((p + 1) + q) (EmS p (q + 1) ((p + 1) + q) h₁)
        + (-1 : ℤ) ^ (p + 1) • (psiSum (p + 1) q).f ((p + 1) + q)
            (EmS (p + 1) q ((p + 1) + q) rfl)
        - dcast (p + 1) (q + 1) h₁
            ((phiSum p (q + 1)).f (p + (q + 1)) (dfc W p (q + 1)))
        - (-1 : ℤ) ^ (p + 1) •
            (psiSum (p + 1) q).f ((p + 1) + q) (dfc W (p + 1) q) := by
    rw [map_sub, map_sub, map_zsmul]
    rw [show (tMod (p + 1) (q + 1)).d ((p + 1) + (q + 1)) ((p + 1) + (q + 1) - 1)
        (Em (p + 1) (q + 1))
        = (tMod (p + 1) (q + 1)).d (((p + 1) + q) + 1) ((p + 1) + q) (Em (p + 1) (q + 1))
        from rfl, hEm, hphi, hpsi]
  rw [show (tMod (p + 1) (q + 1)).d ((p + 1) + (q + 1)) ((p + 1) + (q + 1) - 1)
      (dfc W (p + 1) (q + 1))
      = (tMod (p + 1) (q + 1)).d ((p + 1) + (q + 1)) ((p + 1) + (q + 1) - 1)
        (Em (p + 1) (q + 1) - phiTsum W p (q + 1)
          - (-1 : ℤ) ^ (p + 1) • psiTsum W (p + 1) q) from by
    rw [dfc_eq_dfc2]
    rw [show dfc2 W (p + 1) (q + 1) = Em (p + 1) (q + 1) - phiTsum W p (q + 1)
        - (-1 : ℤ) ^ (p + 1) • psiTsum W (p + 1) q from rfl], hexp]
  -- combine the two `dcast`s and the two subtractions
  rw [hEE, hES]
  have hre : dcast (p + 1) (q + 1) h₁ ((phiSum p (q + 1)).f (p + (q + 1)) (Em p (q + 1)))
        + (-1 : ℤ) ^ (p + 1) • (psiSum (p + 1) q).f ((p + 1) + q) (Em (p + 1) q)
        - dcast (p + 1) (q + 1) h₁
            ((phiSum p (q + 1)).f (p + (q + 1)) (dfc W p (q + 1)))
        - (-1 : ℤ) ^ (p + 1) • (psiSum (p + 1) q).f ((p + 1) + q) (dfc W (p + 1) q)
      = (dcast (p + 1) (q + 1) h₁ ((phiSum p (q + 1)).f (p + (q + 1)) (Em p (q + 1)))
          - dcast (p + 1) (q + 1) h₁
              ((phiSum p (q + 1)).f (p + (q + 1)) (dfc W p (q + 1))))
        + (-1 : ℤ) ^ (p + 1) •
            ((psiSum (p + 1) q).f ((p + 1) + q) (Em (p + 1) q)
              - (psiSum (p + 1) q).f ((p + 1) + q) (dfc W (p + 1) q)) := by
    rw [smul_sub_mod]
    abel
  rw [hre, ← dcast_sub (p + 1) (q + 1) h₁]
  rw [show (psiSum (p + 1) q).f ((p + 1) + q) (Em (p + 1) q)
        - (psiSum (p + 1) q).f ((p + 1) + q) (dfc W (p + 1) q)
        = (psiSum (p + 1) q).f ((p + 1) + q) (Em (p + 1) q - dfc W (p + 1) q) from
      (map_sub _ _ _).symm]
  rw [show (phiSum p (q + 1)).f (p + (q + 1)) (Em p (q + 1))
        - (phiSum p (q + 1)).f (p + (q + 1)) (dfc W p (q + 1))
        = (phiSum p (q + 1)).f (p + (q + 1)) (Em p (q + 1) - dfc W p (q + 1)) from
      (map_sub _ _ _).symm]

/-- The defect `Em p (q+1) - dfc W p (q+1)`, expanded. -/
lemma Em_sub_dfc_shift (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ) :
    Em p (q + 1) - dfc W p (q + 1)
      = match p with
        | 0 => psiTsum W 0 q
        | p' + 1 => phiTsum W p' (q + 1) + (-1 : ℤ) ^ (p' + 1) • psiTsum W (p' + 1) q := by
  rcases p with _ | p'
  · rw [dfc_eq_dfc2]
    rw [show dfc2 W 0 (q + 1) = Em 0 (q + 1) - psiTsum W 0 q from rfl]
    abel
  · rw [dfc_eq_dfc2]
    rw [show dfc2 W (p' + 1) (q + 1) = Em (p' + 1) (q + 1) - phiTsum W p' (q + 1)
        - (-1 : ℤ) ^ (p' + 1) • psiTsum W (p' + 1) q from rfl]
    abel

/-- The defect `Em (p+1) q - dfc W (p+1) q`, expanded. -/
lemma Em_sub_dfc_shift' (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ) :
    Em (p + 1) q - dfc W (p + 1) q
      = match q with
        | 0 => phiTsum W p 0
        | q' + 1 => phiTsum W p (q' + 1) + (-1 : ℤ) ^ (p + 1) • psiTsum W (p + 1) q' := by
  rcases q with _ | q'
  · rw [dfc_eq_dfc2]
    rw [show dfc2 W (p + 1) 0 = Em (p + 1) 0 - phiTsum W p 0 from rfl]
    abel
  · rw [dfc_eq_dfc2]
    rw [show dfc2 W (p + 1) (q' + 1) = Em (p + 1) (q' + 1) - phiTsum W p (q' + 1)
        - (-1 : ℤ) ^ (p + 1) • psiTsum W (p + 1) q' from rfl]
    abel

/-- The cycle condition for the pair `(1,1)`. -/
theorem dfc_cycle_pp_00 (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (hW : ∀ p' q', p' + q' < 1 + 1 →
      (tMod p' q').d (p' + q' + 1) (p' + q') (W p' q') = dfc W p' q') :
    (tMod 1 1).d (1 + 1) (1 + 1 - 1) (dfc W 1 1) = 0 := by
  have hred : (tMod 1 1).d (1 + 1) (1 + 1 - 1) (dfc W 1 1)
      = (tMod 1 1).d (1 + 1) (1 + 1 - 1)
          (Em 1 1 - phiTsum W 0 1 - (-1 : ℤ) ^ 1 • psiTsum W 1 0) := by
    rw [dfc_eq_dfc2]
    rw [show dfc2 W 1 1 = Em 1 1 - phiTsum W 0 1 - (-1 : ℤ) ^ 1 • psiTsum W 1 0 from rfl]
  rw [hred, map_sub, map_sub, map_zsmul]
  have hEm : (tMod 1 1).d (1 + 1) (1 + 1 - 1) (Em 1 1)
      = (phiSum 0 1).f 1 (Em 0 1) + (-1 : ℤ) ^ 1 • (psiSum 1 0).f 1 (Em 1 0) := by
    have hb := ezaw_boundary_pp 0 0 1 rfl rfl rfl
    rw [show EmS 1 1 (1 + 1) rfl = Em 1 1 from EmS_self 1 1,
      show EmS 0 1 1 rfl = Em 0 1 from by
        rw [show EmS 0 1 1 rfl = EmS 0 1 (0 + 1) rfl from rfl]; exact EmS_self 0 1,
      show EmS 1 0 1 rfl = Em 1 0 from by
        rw [show EmS 1 0 1 rfl = EmS 1 0 (1 + 0) rfl from rfl]; exact EmS_self 1 0] at hb
    exact hb
  have hphi : (tMod 1 1).d (1 + 1) (1 + 1 - 1) (phiTsum W 0 1)
      = (phiSum 0 1).f 1 (Em 0 1) - (phiSum 0 1).f 1 (psiTsum W 0 0) := by
    have hd1 := d_phiTsum W 0 1 (hW 0 1 (by norm_num))
    have hX : dcast 1 1 (congrArg (fun k => k - 1) (Nat.add_right_comm 0 1 1).symm)
        ((phiSum 0 1).f (0 + 1) (dfc W 0 1)) = (phiSum 0 1).f (0 + 1) (dfc W 0 1) := by
      rw [Subsingleton.elim (congrArg (fun k => k - 1) (Nat.add_right_comm 0 1 1).symm)
        (rfl : 0 + 1 = 0 + 1), dcast_rfl]
    rw [hd1, hX]
    have hdf : dfc W 0 1 = Em 0 1 - psiTsum W 0 0 := by
      rw [dfc_eq_dfc2]
      rfl
    rw [hdf, map_sub]
  have hpsi : (tMod 1 1).d (1 + 1) (1 + 1 - 1) (psiTsum W 1 0)
      = (psiSum 1 0).f 1 (Em 1 0) - (psiSum 1 0).f 1 (phiTsum W 0 0) := by
    have hd1 := d_psiTsum W 1 0 (hW 1 0 (by norm_num))
    rw [hd1]
    have hdf : dfc W 1 0 = Em 1 0 - phiTsum W 0 0 := by
      rw [dfc_eq_dfc2]
      rfl
    rw [hdf, map_sub]
  have hphi00 : phiTsum W 0 0 = (phiSum 0 0).f (0 + 0 + 1) (W 0 0) := by
    rw [show phiTsum W 0 0 = dcast (0 + 1) 0 (Nat.add_right_comm 0 1 0).symm
        ((phiSum 0 0).f (0 + 0 + 1) (W 0 0)) from rfl]
    rw [Subsingleton.elim (Nat.add_right_comm 0 1 0).symm (rfl : 0 + 0 + 1 = 0 + 0 + 1),
      dcast_rfl]
  have hmix : (phiSum 0 1).f 1 (psiTsum W 0 0) = (psiSum 1 0).f 1 (phiTsum W 0 0) := by
    rw [show psiTsum W 0 0 = (psiSum 0 0).f (0 + 0 + 1) (W 0 0) from rfl, hphi00]
    rw [show (phiSum 0 1).f 1 ((psiSum 0 0).f (0 + 0 + 1) (W 0 0))
        = (phiSum 0 1).f (0 + 0 + 1) ((psiSum 0 0).f (0 + 0 + 1) (W 0 0)) from rfl]
    rw [psiSum_phiSum_apply 0 0 (0 + 0 + 1) (W 0 0)]
  rw [hEm, hphi, hpsi, show (-1 : ℤ) ^ 1 = -1 by norm_num, hmix]
  abel

/-! ## The degree-transport toolkit for the cycle condition -/

/-- A degree transport cancels the transport in the opposite direction. -/
lemma dcast_symm_cancel (p q : ℕ) {n m : ℕ} (h : n = m) (x : ↥((tMod p q).X n)) :
    dcast p q h.symm (dcast p q h x) = x := by
  rw [dcast_trans (p := p) (q := q) (h1 := h.symm) (h2 := h) x,
    dcast_congr p q (h := h.trans h.symm) (h' := rfl) x, dcast_rfl]

/-- A degree transport cancels the transport in the opposite direction. -/
lemma dcast_symm_cancel' (p q : ℕ) {n m : ℕ} (h : n = m) (x : ↥((tMod p q).X m)) :
    dcast p q h (dcast p q h.symm x) = x := by
  rw [dcast_trans (p := p) (q := q) (h1 := h) (h2 := h.symm) x,
    dcast_congr p q (h := h.symm.trans h) (h' := rfl) x, dcast_rfl]

/-- A degree transport along a reflexivity-shaped equality is the identity. -/
lemma dcast_self (p q : ℕ) {n : ℕ} (h : n = n) (x : ↥((tMod p q).X n)) :
    dcast p q h x = x := by
  rw [Subsingleton.elim h rfl, dcast_rfl]

/-- Pushing a degree transport through the first coface sum. -/
lemma dcast_phiSum (p q : ℕ) {n m : ℕ} (h : n = m) (x : ↥((tMod p q).X n)) :
    (phiSum p q).f m (dcast p q h x) = dcast (p + 1) q h ((phiSum p q).f n x) :=
  dcast_chainMap' p q (p + 1) q (phiSum p q) h x

/-- Pushing a degree transport through the second coface sum. -/
lemma dcast_psiSum (p q : ℕ) {n m : ℕ} (h : n = m) (x : ↥((tMod p q).X n)) :
    (psiSum p q).f m (dcast p q h x) = dcast p (q + 1) h ((psiSum p q).f n x) :=
  dcast_chainMap' p q p (q + 1) (psiSum p q) h x

/-- The coface sum applied to the universal element is the transport of `phiTsum`. -/
lemma phiSum_W (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ) :
    (phiSum p q).f (p + q + 1) (W p q)
      = dcast (p + 1) q (Nat.add_right_comm p 1 q) (phiTsum W p q) := by
  rw [show phiTsum W p q = dcast (p + 1) q (Nat.add_right_comm p 1 q).symm
      ((phiSum p q).f (p + q + 1) (W p q)) from rfl]
  exact (dcast_symm_cancel' (p + 1) q (Nat.add_right_comm p 1 q)
    ((phiSum p q).f (p + q + 1) (W p q))).symm

/-- `psiTsum` in terms of the coface sum. -/
lemma psiTsum_eq_psiSum (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ) :
    psiTsum W p q = (psiSum p q).f (p + (q + 1)) (W p q) := rfl

/-- `(-1)^(n+2) = -(-1)^(n+1)`. -/
lemma neg_one_pow_add_two (n : ℕ) : (-1 : ℤ) ^ (n + 2) = -((-1 : ℤ) ^ (n + 1)) := by
  rw [show n + 2 = n + 1 + 1 by omega, pow_succ]
  ring

/-- `-1 • x = -x` for a `ℤ`-module. -/
lemma neg_one_smul_mod {M : Type*} [AddCommGroup M] [Module ℤ M] (x : M) :
    (-1 : ℤ) • x = -x := by
  simp

/-- **The reduction of the cycle condition** to the two transported lower defects. -/
lemma dfc_cycle_red2 (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (p q : ℕ) (h₁ : p + (q + 1) = (p + 1) + q)
    (hW : ∀ p' q', p' + q' < (p + 1) + (q + 1) →
      (tMod p' q').d (p' + q' + 1) (p' + q') (W p' q') = dfc W p' q') :
    (tMod (p + 1) (q + 1)).d ((p + 1) + (q + 1)) ((p + 1) + (q + 1) - 1)
        (dfc W (p + 1) (q + 1))
      = (phiSum p (q + 1)).f ((p + 1) + q)
          (dcast p (q + 1) h₁ (Em p (q + 1) - dfc W p (q + 1)))
        + (-1 : ℤ) ^ (p + 1) • (psiSum (p + 1) q).f ((p + 1) + q)
            (Em (p + 1) q - dfc W (p + 1) q) := by
  rw [dfc_cycle_pp_red W p q h₁ hW,
    (dcast_chainMap' p (q + 1) (p + 1) (q + 1) (phiSum p (q + 1)) h₁
      (Em p (q + 1) - dfc W p (q + 1))).symm]

/-- The cycle condition in the case `(p+1,q+1)`. -/
theorem dfc_cycle_pp (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1))) (p q : ℕ)
    (hW : ∀ p' q', p' + q' < (p + 1) + (q + 1) →
      (tMod p' q').d (p' + q' + 1) (p' + q') (W p' q') = dfc W p' q') :
    (tMod (p + 1) (q + 1)).d ((p + 1) + (q + 1)) ((p + 1) + (q + 1) - 1)
      (dfc W (p + 1) (q + 1)) = 0 := by
  rcases p with _ | p' <;> rcases q with _ | q'
  · -- `(0,0)`: the pair `(1,1)`
    exact dfc_cycle_pp_00 W hW
  · -- `(0, q'+1)`: the pair `(1, q'+2)`
    have h₁ : 0 + (q' + 1) + 1 = (0 + 1) + (q' + 1) := by omega
    rw [dfc_cycle_red2 W 0 (q' + 1) h₁ hW]
    have hX : dcast 0 (q' + 1 + 1) h₁ (Em 0 (q' + 1 + 1) - dfc W 0 (q' + 1 + 1))
        = dcast 0 (q' + 1 + 1) h₁ (psiTsum W 0 (q' + 1)) := by
      rw [Em_sub_dfc_shift W 0 (q' + 1)]
    have hY : Em (0 + 1) (q' + 1) - dfc W (0 + 1) (q' + 1)
        = phiTsum W 0 (q' + 1) + (-1 : ℤ) ^ (0 + 1) • psiTsum W (0 + 1) q' := by
      rw [Em_sub_dfc_shift' W 0 (q' + 1)]
    rw [hX, hY, map_add, map_zsmul, smul_add_mod]
    have hS : (psiSum (0 + 1) (q' + 1)).f ((0 + 1) + (q' + 1))
        (psiTsum W (0 + 1) q') = 0 := by
      rw [show psiTsum W (0 + 1) q'
          = (psiSum (0 + 1) q').f ((0 + 1) + q' + 1) (W (0 + 1) q') from rfl]
      exact psiSum_comp_apply (0 + 1) q' ((0 + 1) + q' + 1) (W (0 + 1) q')
    have hM : (phiSum 0 (q' + 1 + 1)).f ((0 + 1) + (q' + 1))
          (dcast 0 (q' + 1 + 1) h₁ (psiTsum W 0 (q' + 1)))
        = (psiSum (0 + 1) (q' + 1)).f ((0 + 1) + (q' + 1)) (phiTsum W 0 (q' + 1)) := by
      rw [show psiTsum W 0 (q' + 1)
          = (psiSum 0 (q' + 1)).f (0 + (q' + 1) + 1) (W 0 (q' + 1)) from rfl]
      rw [dcast_chainMap' 0 (q' + 1 + 1) (0 + 1) (q' + 1 + 1) (phiSum 0 (q' + 1 + 1)) h₁]
      rw [psiSum_phiSum_apply 0 (q' + 1) (0 + (q' + 1) + 1) (W 0 (q' + 1))]
      rw [phiSum_W W 0 (q' + 1)]
      rw [dcast_psiSum (0 + 1) (q' + 1) (Nat.add_right_comm 0 1 (q' + 1))]
      rw [dcast_trans (p := 0 + 1) (q := q' + 1 + 1) (h1 := h₁)
        (h2 := Nat.add_right_comm 0 1 (q' + 1))]
      rw [Subsingleton.elim ((Nat.add_right_comm 0 1 (q' + 1)).trans h₁)
        (rfl : ((0 + 1) + (q' + 1)) = ((0 + 1) + (q' + 1))), dcast_rfl]
    rw [hM, hS]
    simp only [smul_zero, add_zero]
    rw [show (-1 : ℤ) ^ (0 + 1) = -1 by norm_num, neg_one_smul_mod]
    abel
  · -- `(p'+1, 0)`: the pair `(p'+2, 1)`
    have h₁ : (p' + 1) + (0 + 1) = ((p' + 1) + 1) + 0 := by omega
    rw [dfc_cycle_red2 W (p' + 1) 0 h₁ hW]
    have hX : dcast (p' + 1) (0 + 1) h₁ (Em (p' + 1) (0 + 1) - dfc W (p' + 1) (0 + 1))
        = dcast (p' + 1) (0 + 1) h₁ (phiTsum W p' (0 + 1))
          + (-1 : ℤ) ^ (p' + 1) •
              dcast (p' + 1) (0 + 1) h₁ (psiTsum W (p' + 1) 0) := by
      rw [Em_sub_dfc_shift W (p' + 1) 0, dcast_add, dcast_smul]
    have hY : Em ((p' + 1) + 1) 0 - dfc W ((p' + 1) + 1) 0 = phiTsum W (p' + 1) 0 := by
      rw [Em_sub_dfc_shift' W (p' + 1) 0]
    rw [hX, hY, map_add, map_zsmul]
    have hA : (phiSum (p' + 1) (0 + 1)).f (((p' + 1) + 1) + 0)
        (dcast (p' + 1) (0 + 1) h₁ (phiTsum W p' (0 + 1))) = 0 := by
      rw [dcast_self (p' + 1) (0 + 1) h₁ (phiTsum W p' (0 + 1))]
      rw [show phiTsum W p' (0 + 1)
          = dcast (p' + 1) (0 + 1) (Nat.add_right_comm p' 1 (0 + 1)).symm
              ((phiSum p' (0 + 1)).f (p' + (0 + 1) + 1) (W p' (0 + 1))) from rfl]
      rw [dcast_self (p' + 1) (0 + 1) (Nat.add_right_comm p' 1 (0 + 1)).symm _]
      rw [show (phiSum (p' + 1) (0 + 1)).f (((p' + 1) + 1) + 0)
            ((phiSum p' (0 + 1)).f (p' + (0 + 1) + 1) (W p' (0 + 1)))
          = (phiSum (p' + 1) (0 + 1)).f (p' + (0 + 1) + 1)
              ((phiSum p' (0 + 1)).f (p' + (0 + 1) + 1) (W p' (0 + 1))) from rfl]
      exact phiSum_comp_apply p' (0 + 1) (p' + (0 + 1) + 1) (W p' (0 + 1))
    have hM : (phiSum (p' + 1) (0 + 1)).f (((p' + 1) + 1) + 0)
          (dcast (p' + 1) (0 + 1) h₁ (psiTsum W (p' + 1) 0))
        = (psiSum ((p' + 1) + 1) 0).f (((p' + 1) + 1) + 0) (phiTsum W (p' + 1) 0) := by
      rw [dcast_self (p' + 1) (0 + 1) h₁ (psiTsum W (p' + 1) 0)]
      rw [show psiTsum W (p' + 1) 0
          = (psiSum (p' + 1) 0).f ((p' + 1) + 0 + 1) (W (p' + 1) 0) from rfl]
      rw [show (phiSum (p' + 1) (0 + 1)).f (((p' + 1) + 1) + 0)
            ((psiSum (p' + 1) 0).f ((p' + 1) + 0 + 1) (W (p' + 1) 0))
          = (phiSum (p' + 1) (0 + 1)).f ((p' + 1) + 0 + 1)
              ((psiSum (p' + 1) 0).f ((p' + 1) + 0 + 1) (W (p' + 1) 0)) from rfl]
      rw [psiSum_phiSum_apply (p' + 1) 0 ((p' + 1) + 0 + 1) (W (p' + 1) 0)]
      rw [phiSum_W W (p' + 1) 0]
      rw [show (psiSum ((p' + 1) + 1) 0).f (((p' + 1) + 1) + 0)
            (dcast ((p' + 1) + 1) 0 (Nat.add_right_comm (p' + 1) 1 0)
              (phiTsum W (p' + 1) 0))
          = (psiSum ((p' + 1) + 1) 0).f ((p' + 1) + 0 + 1)
              (dcast ((p' + 1) + 1) 0 (Nat.add_right_comm (p' + 1) 1 0)
                (phiTsum W (p' + 1) 0)) from rfl]
      rw [dcast_psiSum ((p' + 1) + 1) 0 (Nat.add_right_comm (p' + 1) 1 0)]
      rw [dcast_self ((p' + 1) + 1) (0 + 1) (Nat.add_right_comm (p' + 1) 1 0) _]
    rw [hA, hM]
    rw [show (-1 : ℤ) ^ ((p' + 1) + 1) = -((-1 : ℤ) ^ (p' + 1)) by
      rw [pow_succ]; ring]
    rw [neg_zsmul]
    simp only [zero_add]
    abel
  · -- `(p'+1, q'+1)`: the pair `(p'+2, q'+2)`
    have h₁ : (p' + 1) + ((q' + 1) + 1) = ((p' + 1) + 1) + (q' + 1) := by omega
    rw [dfc_cycle_red2 W (p' + 1) (q' + 1) h₁ hW]
    have hX : dcast (p' + 1) ((q' + 1) + 1) h₁
          (Em (p' + 1) ((q' + 1) + 1) - dfc W (p' + 1) ((q' + 1) + 1))
        = dcast (p' + 1) ((q' + 1) + 1) h₁ (phiTsum W p' ((q' + 1) + 1))
          + (-1 : ℤ) ^ (p' + 1) •
              dcast (p' + 1) ((q' + 1) + 1) h₁ (psiTsum W (p' + 1) (q' + 1)) := by
      rw [Em_sub_dfc_shift W (p' + 1) (q' + 1), dcast_add, dcast_smul]
    have hY : Em ((p' + 1) + 1) (q' + 1) - dfc W ((p' + 1) + 1) (q' + 1)
        = phiTsum W (p' + 1) (q' + 1)
          + (-1 : ℤ) ^ ((p' + 1) + 1) • psiTsum W ((p' + 1) + 1) q' := by
      rw [Em_sub_dfc_shift' W (p' + 1) (q' + 1)]
    rw [hX, hY, map_add, map_zsmul, map_add, map_zsmul, smul_add_mod]
    -- (A) the `phiphi` term vanishes
    have hA : (phiSum (p' + 1) ((q' + 1) + 1)).f (((p' + 1) + 1) + (q' + 1))
        (dcast (p' + 1) ((q' + 1) + 1) h₁ (phiTsum W p' ((q' + 1) + 1))) = 0 := by
      rw [dcast_chainMap' (p' + 1) ((q' + 1) + 1) ((p' + 1) + 1) ((q' + 1) + 1)
        (phiSum (p' + 1) ((q' + 1) + 1)) h₁]
      rw [show phiTsum W p' ((q' + 1) + 1)
          = dcast (p' + 1) ((q' + 1) + 1) (Nat.add_right_comm p' 1 ((q' + 1) + 1)).symm
              ((phiSum p' ((q' + 1) + 1)).f (p' + ((q' + 1) + 1) + 1)
                (W p' ((q' + 1) + 1))) from rfl]
      rw [dcast_chainMap' (p' + 1) ((q' + 1) + 1) ((p' + 1) + 1) ((q' + 1) + 1)
        (phiSum (p' + 1) ((q' + 1) + 1)) (Nat.add_right_comm p' 1 ((q' + 1) + 1)).symm]
      rw [phiSum_comp_apply p' ((q' + 1) + 1) (p' + ((q' + 1) + 1) + 1)
        (W p' ((q' + 1) + 1))]
      rw [dcast_zero, dcast_zero]
    -- (D) the `psipsi` term vanishes
    have hS : (psiSum ((p' + 1) + 1) (q' + 1)).f (((p' + 1) + 1) + (q' + 1))
        (psiTsum W ((p' + 1) + 1) q') = 0 := by
      rw [show psiTsum W ((p' + 1) + 1) q'
          = (psiSum ((p' + 1) + 1) q').f (((p' + 1) + 1) + q' + 1)
              (W ((p' + 1) + 1) q') from rfl]
      rw [show (psiSum ((p' + 1) + 1) (q' + 1)).f (((p' + 1) + 1) + (q' + 1))
            ((psiSum ((p' + 1) + 1) q').f (((p' + 1) + 1) + q' + 1)
              (W ((p' + 1) + 1) q'))
          = (psiSum ((p' + 1) + 1) (q' + 1)).f (((p' + 1) + 1) + q' + 1)
            ((psiSum ((p' + 1) + 1) q').f (((p' + 1) + 1) + q' + 1)
              (W ((p' + 1) + 1) q')) from rfl]
      exact psiSum_comp_apply ((p' + 1) + 1) q' (((p' + 1) + 1) + q' + 1)
        (W ((p' + 1) + 1) q')
    -- the mixed terms coincide
    have hM : (phiSum (p' + 1) ((q' + 1) + 1)).f (((p' + 1) + 1) + (q' + 1))
          (dcast (p' + 1) ((q' + 1) + 1) h₁ (psiTsum W (p' + 1) (q' + 1)))
        = (psiSum ((p' + 1) + 1) (q' + 1)).f (((p' + 1) + 1) + (q' + 1))
            (phiTsum W (p' + 1) (q' + 1)) := by
      rw [show psiTsum W (p' + 1) (q' + 1)
          = (psiSum (p' + 1) (q' + 1)).f ((p' + 1) + (q' + 1) + 1)
              (W (p' + 1) (q' + 1)) from rfl]
      rw [dcast_chainMap' (p' + 1) ((q' + 1) + 1) ((p' + 1) + 1) ((q' + 1) + 1)
        (phiSum (p' + 1) ((q' + 1) + 1)) h₁]
      rw [show (phiSum (p' + 1) ((q' + 1) + 1)).f ((p' + 1) + ((q' + 1) + 1))
            ((psiSum (p' + 1) (q' + 1)).f ((p' + 1) + (q' + 1) + 1)
              (W (p' + 1) (q' + 1)))
          = (phiSum (p' + 1) ((q' + 1) + 1)).f ((p' + 1) + (q' + 1) + 1)
            ((psiSum (p' + 1) (q' + 1)).f ((p' + 1) + (q' + 1) + 1)
              (W (p' + 1) (q' + 1))) from rfl]
      rw [psiSum_phiSum_apply (p' + 1) (q' + 1) ((p' + 1) + (q' + 1) + 1)
        (W (p' + 1) (q' + 1))]
      rw [phiSum_W W (p' + 1) (q' + 1)]
      rw [dcast_psiSum ((p' + 1) + 1) (q' + 1) (Nat.add_right_comm (p' + 1) 1 (q' + 1))]
      rw [dcast_trans (p := (p' + 1) + 1) (q := (q' + 1) + 1) (h1 := h₁)
        (h2 := Nat.add_right_comm (p' + 1) 1 (q' + 1))]
      rw [dcast_self ((p' + 1) + 1) ((q' + 1) + 1)
        ((Nat.add_right_comm (p' + 1) 1 (q' + 1)).trans h₁) _]
    rw [hA, hS, hM]
    rw [show (-1 : ℤ) ^ ((p' + 1) + 1) = -((-1 : ℤ) ^ (p' + 1)) by
      rw [pow_succ]; ring]
    rw [neg_zsmul]
    simp only [smul_zero, zero_add, add_zero]
    abel

/-- **The cycle condition**: the defect `dfc W p q` of the recursion is a cycle whenever the
recursion equations hold one level below. -/
theorem dfc_cycle (W : (p q : ℕ) → ↥((tMod p q).X (p + q + 1)))
    (p q : ℕ) (hpq : 1 ≤ p + q)
    (hW : ∀ p' q', p' + q' < p + q →
      (tMod p' q').d (p' + q' + 1) (p' + q') (W p' q') = dfc W p' q') :
    (tMod p q).d (p + q) (p + q - 1) (dfc W p q) = 0 := by
  rcases p with _ | p' <;> rcases q with _ | q'
  · exact dfc_cycle_zz W
  · exact dfc_cycle_zp W q' hW
  · exact dfc_cycle_pz W p' hW
  · exact dfc_cycle_pp W p' q' hW

end

end Work.Kunneth
