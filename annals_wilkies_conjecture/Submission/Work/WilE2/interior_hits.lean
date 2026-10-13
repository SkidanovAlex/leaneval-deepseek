/-
  Work.WilE2 — `interior_hits`.

  **The reduction.**  The components of `X = cubeC k ∩ Zset c g` are hit inside the *interior* of
  the cube by the *ball* statement (`Work.WilE2.euclidean_ball_components`, GV Corollary 3.3)
  applied to a *fattened* variety.  The cube `[-1,1]^k` is the projection of the compact torus

      T = {(x,t) ∈ ℝ^k × ℝ^k | ∀ i, xᵢ² + tᵢ² = 1}

  (for `x ∈ [-1,1]^k` take `tᵢ = √(1-xᵢ²)`), and the *variety*

      Z̃ = {(x,t) ∈ T | x ∈ Zset c g}

  — the zero set of the *padded* equations together with the `k` sphere equations — projects onto
  exactly `cubeC k ∩ Zset c g`.  Every component of `Z̃` maps into a component of `X`, so a finite
  hitting set for the components of `Z̃` projects to a set of points of `X`; the ball statement
  produces such a hitting set, because `Z̃ ⊆ {z | ∑ zᵢ² ≤ (√k)²}` (summing the sphere equations
  gives `∑ zᵢ² = k`), i.e. `Z̃` is *compact* and inside the ball of radius `√k`.

  Concretely: for `x` in the interior of the cube, `(x,t) ∈ Z̃` for `tᵢ = √(1-xᵢ²)`; the ball
  statement gives a hit `vHat ∈ sB` in the same component of `Z̃` as `(x,t)`; projecting gives
  `y = takeZ hm vHat`, which lies in `X` and in the same component of `X` as `x`.  So
  `s = sB.image (takeZ hm)` is the required finite set.

  The cardinality bookkeeping is polynomial: padding an equation does not raise `atomDeg`
  (`MvPolynomial.totalDegree_rename_le`) and each of the `k ≤ F` sphere equations contributes
  `atomDeg = 3`.

  The single input is therefore the ball statement — GV Corollary 3.3 — which is exactly the
  sibling target `Work.WilE2.euclidean_ball_components`; everything in this file is bookkeeping
  around it.

  **The input.**  The ball statement is proved in the shared E2 library as
  `Work.WilE2.Cb.ball_components` (assembled from `Ebc.tube_separation`,
  `Ebc.exists_regular_epsilon`, `Ebc.component_locally_level`, `Ebc.hits_of_count`,
  `Cb.exists_good_point`, `Cb.exists_generic_slope` and `Cb.good_card_le`), so `interior_hits`
  below is the one-line application of the reduction proved here.  The auxiliary `Ebc`/`Cb` pieces
  are the Milnor/Petrovskii–Oleinik device: the tube `D_ε = {∑ f² + ε(‖x‖²-ρ²) ≤ 0}` separates the
  components of `Zset c g` for small `ε`, its boundary `{F_ε = 0}` is a smooth compact hypersurface
  on which a generic linear functional has nondegenerate Lagrange points, and `hE2a` counts those
  as the nondegenerate solutions of the square EA system `F_ε = 0, ∂_jF_ε - sl_j∂_{i₀}F_ε = 0`.
-/
import Mathlib
import Submission.Work.WilE2.VcbDefs
import Submission.Work.WilE2.VcbTopology
import Submission.Work.WilE2.Cb.ball_components
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.pad_eval
import Submission.Work.WilE5.Cells.khovCount

set_option autoImplicit false
noncomputable section

namespace Work.WilE2

open Classical Set
open WilkiesDesign WilkiesDesign.E

variable {k r : ℕ}

/-! ## §1. The doubled space `Fin (k+k)`: first block `x`, second block `t` -/

/-- The first block of `Fin.append x t` is `x`. -/
theorem takeZ_append (hm : k ≤ k + k) (x : Fin k → ℝ) (t : Fin k → ℝ) :
    Work.WilE7.takeZ hm (Fin.append x t) = x := by
  funext i
  show Fin.append x t ⟨i.val, lt_of_lt_of_le i.isLt hm⟩ = x i
  have h : (⟨i.val, lt_of_lt_of_le i.isLt hm⟩ : Fin (k + k)) = Fin.castAdd k i := Fin.ext rfl
  rw [h, Fin.append_left]

/-- `takeZ` is the projection onto the first block. -/
theorem takeZ_apply (hm : k ≤ k + k) (y : Fin (k + k) → ℝ) (i : Fin k) :
    Work.WilE7.takeZ hm y i = y (Fin.castLE hm i) := rfl

theorem continuous_takeZ (hm : k ≤ k + k) : Continuous (Work.WilE7.takeZ hm) := by
  refine continuous_pi fun i => ?_
  have h : (fun y : Fin (k + k) → ℝ => Work.WilE7.takeZ hm y i)
      = fun y : Fin (k + k) → ℝ => y (Fin.castLE hm i) := rfl
  rw [h]
  exact continuous_apply _

/-- The sphere equation `xᵢ² + tᵢ² - 1` on the doubled space. -/
def sphPoly {k : ℕ} (r : ℕ) (hm : k ≤ k + k) (i : Fin k) : EAPoly (k + k) r :=
  (MvPolynomial.X (Sum.inl (Fin.castLE hm i)) : EAPoly (k + k) r) ^ 2 +
    (MvPolynomial.X (Sum.inl (Fin.natAdd k i)) : EAPoly (k + k) r) ^ 2 + MvPolynomial.C (-1)

/-- The fattened family: the padded equations together with the `k` sphere equations. -/
def extFam (hm : k ≤ k + k) (g : Finset (EAPoly k r)) : Finset (EAPoly (k + k) r) :=
  (g.image (Work.WilE7.EAPoly.pad hm)) ∪ (Finset.univ.image (sphPoly r hm))

theorem eaEval_sphPoly (hm : k ≤ k + k) (c : EAChain k r) (i : Fin k) (y : Fin (k + k) → ℝ) :
    eaEval (Work.WilE7.EAChain.pad hm c) (sphPoly r hm i) y
      = (y (Fin.castLE hm i)) ^ 2 + (y (Fin.natAdd k i)) ^ 2 - 1 := by
  simp only [sphPoly, eaEval, map_add, MvPolynomial.eval_pow, MvPolynomial.eval_X,
    MvPolynomial.eval_C, Sum.elim_inl]
  ring

/-- Membership in the fattened zero set. -/
theorem mem_extFam_Zset (hm : k ≤ k + k) (c : EAChain k r) (g : Finset (EAPoly k r))
    (y : Fin (k + k) → ℝ) :
    y ∈ Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g) ↔
      (∀ f ∈ g, eaEval c f (Work.WilE7.takeZ hm y) = 0) ∧
      (∀ i : Fin k, (y (Fin.castLE hm i)) ^ 2 + (y (Fin.natAdd k i)) ^ 2 = 1) := by
  simp only [Zset, Set.mem_ofPred_eq, extFam, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro f hf
      have h1 := h (Work.WilE7.EAPoly.pad hm f) (Or.inl ⟨f, hf, rfl⟩)
      rw [Work.WilE7.padAux.eaEval_pad] at h1
      exact h1
    · intro i
      have h1 := h (sphPoly r hm i) (Or.inr ⟨i, rfl⟩)
      rw [eaEval_sphPoly hm c i y] at h1
      linarith
  · rintro ⟨h1, h2⟩ Q (⟨f, hf, rfl⟩ | ⟨i, rfl⟩)
    · rw [Work.WilE7.padAux.eaEval_pad]
      exact h1 f hf
    · rw [eaEval_sphPoly hm c i y]
      have := h2 i
      linarith

/-! ## §2. Degree bookkeeping -/

theorem atomDeg_pad_le (hm : k ≤ k + k) (f : EAPoly k r) :
    atomDeg (Work.WilE7.EAPoly.pad hm f) ≤ atomDeg f := by
  unfold atomDeg
  exact Nat.add_le_add_right (MvPolynomial.totalDegree_rename_le _ f) 1

theorem atomDeg_sphPoly_le (hm : k ≤ k + k) (i : Fin k) :
    atomDeg (sphPoly r hm i) ≤ 3 := by
  have hX1 : (((MvPolynomial.X (Sum.inl (Fin.castLE hm i)) : EAPoly (k + k) r)) ^ 2).totalDegree
      ≤ 2 := by
    calc (((MvPolynomial.X (Sum.inl (Fin.castLE hm i)) : EAPoly (k + k) r)) ^ 2).totalDegree
        ≤ 2 * ((MvPolynomial.X (Sum.inl (Fin.castLE hm i)) : EAPoly (k + k) r)).totalDegree :=
          MvPolynomial.totalDegree_pow _ 2
      _ = 2 * 1 := by rw [MvPolynomial.totalDegree_X]
      _ = 2 := by norm_num
  have hX2 : (((MvPolynomial.X (Sum.inl (Fin.natAdd k i)) : EAPoly (k + k) r)) ^ 2).totalDegree
      ≤ 2 := by
    calc (((MvPolynomial.X (Sum.inl (Fin.natAdd k i)) : EAPoly (k + k) r)) ^ 2).totalDegree
        ≤ 2 * ((MvPolynomial.X (Sum.inl (Fin.natAdd k i)) : EAPoly (k + k) r)).totalDegree :=
          MvPolynomial.totalDegree_pow _ 2
      _ = 2 * 1 := by rw [MvPolynomial.totalDegree_X]
      _ = 2 := by norm_num
  have h2 : (((MvPolynomial.X (Sum.inl (Fin.castLE hm i)) : EAPoly (k + k) r)) ^ 2
      + ((MvPolynomial.X (Sum.inl (Fin.natAdd k i)) : EAPoly (k + k) r)) ^ 2).totalDegree
      ≤ 2 :=
    le_trans (MvPolynomial.totalDegree_add _ _) (max_le hX1 hX2)
  have h3 : ((MvPolynomial.C (-1) : EAPoly (k + k) r)).totalDegree ≤ 2 := by
    rw [MvPolynomial.totalDegree_C]; norm_num
  have h : (sphPoly r hm i).totalDegree ≤ 2 :=
    le_trans (MvPolynomial.totalDegree_add _ _) (max_le h2 h3)
  unfold atomDeg
  omega

/-- **The degree bound for the fattened family.** -/
theorem sum_atomDeg_extFam_le (hm : k ≤ k + k) {F : ℕ} (hF : k ≤ F)
    (g : Finset (EAPoly k r)) :
    ∑ Q ∈ extFam hm g, atomDeg Q ≤
      ((Polynomial.X + Polynomial.C (F : ℕ)) *
        (Polynomial.X + Polynomial.C 3)).eval (∑ f ∈ g, atomDeg f) := by
  set D : ℕ := ∑ f ∈ g, atomDeg f with hD
  have hcard : (extFam hm g).card ≤ g.card + k := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have h1 : (g.image (Work.WilE7.EAPoly.pad hm)).card ≤ g.card :=
      Finset.card_image_le (s := g) (f := fun f : EAPoly k r => Work.WilE7.EAPoly.pad hm f)
    have h2 : ((Finset.univ : Finset (Fin k)).image (sphPoly r hm)).card ≤ k := by
      refine le_trans (Finset.card_image_le (s := (Finset.univ : Finset (Fin k)))
        (f := fun i : Fin k => sphPoly r hm i)) ?_
      simp
    omega
  have hgcard : g.card ≤ D := by
    have hle : ∀ f ∈ g, (1 : ℕ) ≤ atomDeg f := by
      intro f _
      have : 0 ≤ f.totalDegree := Nat.zero_le _
      simp only [atomDeg]; omega
    calc g.card = ∑ _f ∈ g, (1 : ℕ) := Finset.card_eq_sum_ones g
      _ ≤ ∑ f ∈ g, atomDeg f := by
          refine Finset.sum_le_sum ?_
          intro f hf
          exact hle f hf
      _ = D := by rw [hD]
  have hpt : ∀ Q ∈ extFam hm g, atomDeg Q ≤ D + 3 := by
    intro Q hQ
    rw [extFam, Finset.mem_union] at hQ
    rcases hQ with hQ | hQ
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hQ
      have h1 : atomDeg (Work.WilE7.EAPoly.pad hm f) ≤ atomDeg f := atomDeg_pad_le hm f
      have h2 : atomDeg f ≤ D := by
        simpa [hD] using Finset.single_le_sum (f := fun f => atomDeg f)
          (fun x _ => Nat.zero_le _) hf
      omega
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hQ
      have := atomDeg_sphPoly_le (r := r) hm i
      omega
  have hsum : ∑ Q ∈ extFam hm g, atomDeg Q ≤ (extFam hm g).card * (D + 3) := by
    calc ∑ Q ∈ extFam hm g, atomDeg Q ≤ ∑ _Q ∈ extFam hm g, (D + 3) :=
          Finset.sum_le_sum hpt
      _ = (extFam hm g).card * (D + 3) := by simp [Finset.sum_const]
  have harith : (extFam hm g).card * (D + 3) ≤ (D + F) * (D + 3) :=
    Nat.mul_le_mul_right _ (by have := hcard; have := hgcard; omega)
  have hfinal : (D + F) * (D + 3) =
      ((Polynomial.X + Polynomial.C (F : ℕ)) * (Polynomial.X + Polynomial.C 3)).eval D := by
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  rw [hfinal] at harith
  exact le_trans hsum harith

/-! ## §3. The projection of the fattened zero set -/

/-- The projection of a point of the fattened zero set lies in `cubeC k ∩ Zset c g`. -/
theorem takeZ_mem_of_mem_extFam_Zset (hm : k ≤ k + k) {c : EAChain k r}
    {g : Finset (EAPoly k r)} {z : Fin (k + k) → ℝ}
    (hz : z ∈ Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g)) :
    Work.WilE7.takeZ hm z ∈ cubeC k ∩ Zset c g := by
  obtain ⟨h1, h2⟩ := (mem_extFam_Zset hm c g z).mp hz
  refine ⟨?_, ?_⟩
  · intro i
    have h3 := h2 i
    have h4 : (z (Fin.castLE hm i)) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (z (Fin.natAdd k i))]
    rw [takeZ_apply]
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  · intro f hf
    exact h1 f hf

/-- The fattened zero set lies in the ball of radius `√k`. -/
theorem extFam_Zset_subset_ball (hm : k ≤ k + k) (c : EAChain k r) (g : Finset (EAPoly k r)) :
    Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g) ⊆
      {y : Fin (k + k) → ℝ | ∑ i, (y i) ^ 2 ≤ (Real.sqrt k) ^ 2} := by
  intro y hy
  obtain ⟨-, h2⟩ := (mem_extFam_Zset hm c g y).mp hy
  have hone : ∀ i : Fin k, (y (Fin.castAdd k i)) ^ 2 + (y (Fin.natAdd k i)) ^ 2 = 1 := by
    intro i
    have h := h2 i
    rwa [show (Fin.castLE hm i : Fin (k + k)) = Fin.castAdd k i from Fin.ext rfl] at h
  have hsum : ∑ j : Fin (k + k), (y j) ^ 2 = (k : ℝ) := by
    rw [Fin.sum_univ_add, ← Finset.sum_add_distrib]
    simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  show ∑ j : Fin (k + k), (y j) ^ 2 ≤ (Real.sqrt k) ^ 2
  rw [hsum, Real.sq_sqrt (Nat.cast_nonneg k)]

/-- The ball condition is automatic on the fattened zero set. -/
theorem extFam_Zset_inter_ball (hm : k ≤ k + k) (c : EAChain k r) (g : Finset (EAPoly k r)) :
    Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g) ∩
        {y : Fin (k + k) → ℝ | ∑ i, (y i) ^ 2 ≤ (Real.sqrt k) ^ 2}
      = Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g) :=
  Set.inter_eq_left.mpr (extFam_Zset_subset_ball hm c g)

/-! ## §4. The reduction: the ball statement implies `interior_hits` -/

/-- **The ball statement in its "compact" form.**  If the variety is contained in the ball, the
ball statement's conclusion is literally the statement that the components of `Zset c g` itself
are hit.  This is the form in which the components bound is consumed by the reduction below. -/
theorem compact_components_bound_of_ball
    (hBall : ∀ (F : ℕ), ∃ p : Polynomial ℕ,
      ∀ (n r : ℕ) (c : EAChain n r) (g : Finset (EAPoly n r)) (R : ℝ), n + r ≤ F →
        ∃ s : Finset (Fin n → ℝ),
          (↑s : Set (Fin n → ℝ)) ⊆ Zset c g ∩ {x | ∑ i, (x i) ^ 2 ≤ R ^ 2} ∧
          s.card ≤ p.eval (∑ f ∈ g, atomDeg f) ∧
          Hits (Zset c g ∩ {x | ∑ i, (x i) ^ 2 ≤ R ^ 2}) s)
    (F : ℕ) :
    ∃ p : Polynomial ℕ,
      ∀ (n r : ℕ) (c : EAChain n r) (g : Finset (EAPoly n r)) (R : ℝ), n + r ≤ F →
        Zset c g ⊆ {x : Fin n → ℝ | ∑ i, (x i) ^ 2 ≤ R ^ 2} →
        ∃ s : Finset (Fin n → ℝ), (↑s : Set (Fin n → ℝ)) ⊆ Zset c g ∧
          s.card ≤ p.eval (∑ f ∈ g, atomDeg f) ∧ Hits (Zset c g) s := by
  obtain ⟨p, hp⟩ := hBall F
  refine ⟨p, ?_⟩
  intro n r c g R hfmt hsub
  obtain ⟨s, hs1, hs2, hs3⟩ := hp n r c g R hfmt
  have hset : Zset c g ∩ {x : Fin n → ℝ | ∑ i, (x i) ^ 2 ≤ R ^ 2} = Zset c g :=
    Set.inter_eq_left.mpr hsub
  refine ⟨s, fun y hy => (hs1 hy).1, hs2, ?_⟩
  intro x hx
  obtain ⟨y, hy, hyc⟩ := hs3 x (hset.symm ▸ hx)
  exact ⟨y, hy, hset ▸ hyc⟩

/-- **The compact components bound implies `interior_hits`.**  Same reduction as
`interior_hits_of_ball`, but consuming the *compact* form of the components bound directly: the
fattened variety `Z̃` is contained in the ball of radius `√k` (`extFam_Zset_subset_ball`), so the
compact statement applies to it with no intersection bookkeeping. -/
theorem interior_hits_of_compact
    (hComp : ∀ (F : ℕ), ∃ p : Polynomial ℕ,
      ∀ (n r : ℕ) (c : EAChain n r) (g : Finset (EAPoly n r)) (R : ℝ), n + r ≤ F →
        Zset c g ⊆ {x | ∑ i, (x i) ^ 2 ≤ R ^ 2} →
        ∃ s : Finset (Fin n → ℝ), (↑s : Set (Fin n → ℝ)) ⊆ Zset c g ∧
          s.card ≤ p.eval (∑ f ∈ g, atomDeg f) ∧ Hits (Zset c g) s)
    (F : ℕ) :
    ∃ p : Polynomial ℕ,
      ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r) (g : Finset (WilkiesDesign.E.EAPoly k r)),
        k + r ≤ F → ∃ s : Finset (Fin k → ℝ),
          (↑s : Set (Fin k → ℝ)) ⊆ WilkiesDesign.E.cubeC k ∩ Work.WilE2.Zset c g ∧
          s.card ≤ p.eval (∑ f ∈ g, WilkiesDesign.E.atomDeg f) ∧
          (∀ x ∈ WilkiesDesign.E.cubeC k ∩ Work.WilE2.Zset c g ∩
              interior (WilkiesDesign.E.cubeC k),
            ∃ y ∈ s, y ∈ connectedComponentIn
              (WilkiesDesign.E.cubeC k ∩ Work.WilE2.Zset c g) x) := by
  obtain ⟨pComp, hpComp⟩ := hComp (3 * F)
  refine ⟨pComp.comp ((Polynomial.X + Polynomial.C (F : ℕ)) *
      (Polynomial.X + Polynomial.C 3)), ?_⟩
  intro k r c g hkr
  have hkF : k ≤ F := by omega
  have hm : k ≤ k + k := by omega
  have hfmt : (k + k) + r ≤ 3 * F := by omega
  obtain ⟨sB, hsB1, hsB2, hsB3⟩ := hpComp (k + k) r (Work.WilE7.EAChain.pad hm c)
    (extFam hm g) (Real.sqrt k) hfmt (extFam_Zset_subset_ball hm c g)
  refine ⟨sB.image (Work.WilE7.takeZ hm), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨yHat, hyHat, rfl⟩ := Finset.mem_image.mp hy
    exact takeZ_mem_of_mem_extFam_Zset hm (hsB1 hyHat)
  · calc (sB.image (Work.WilE7.takeZ hm)).card ≤ sB.card := Finset.card_image_le
      _ ≤ pComp.eval (∑ Q ∈ extFam hm g, atomDeg Q) := hsB2
      _ ≤ pComp.eval (((Polynomial.X + Polynomial.C (F : ℕ)) *
            (Polynomial.X + Polynomial.C 3)).eval (∑ f ∈ g, atomDeg f)) :=
          Work.WilE5.Cells.khovEval_mono (sum_atomDeg_extFam_le hm hkF g)
      _ = (pComp.comp ((Polynomial.X + Polynomial.C (F : ℕ)) *
            (Polynomial.X + Polynomial.C 3))).eval (∑ f ∈ g, atomDeg f) :=
          (Polynomial.eval_comp (p := pComp)
            (q := (Polynomial.X + Polynomial.C (F : ℕ)) * (Polynomial.X + Polynomial.C 3))
            (x := ∑ f ∈ g, atomDeg f)).symm
  · intro x hx
    obtain ⟨⟨hxc, hxz⟩, _⟩ := hx
    set t : Fin k → ℝ := fun i => Real.sqrt (1 - (x i) ^ 2) with ht
    have ht_sq : ∀ i, (t i) ^ 2 = 1 - (x i) ^ 2 := by
      intro i
      rw [ht]
      refine Real.sq_sqrt ?_
      have h := abs_le.mp (hxc i)
      nlinarith [h.1, h.2]
    set uHat : Fin (k + k) → ℝ := Fin.append x t with huHat
    have huHatZ : uHat ∈ Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g) := by
      rw [mem_extFam_Zset hm c g uHat]
      refine ⟨?_, ?_⟩
      · intro f hf
        rw [huHat, takeZ_append hm x t]
        exact hxz f hf
      · intro i
        have h1 : uHat (Fin.castLE hm i) = x i := by
          rw [huHat]
          have h : (Fin.castLE hm i : Fin (k + k)) = Fin.castAdd k i := Fin.ext rfl
          rw [h, Fin.append_left]
        have h2 : uHat (Fin.natAdd k i) = t i := by
          rw [huHat]; exact Fin.append_right x t i
        rw [h1, h2, ht_sq i]
        ring
    obtain ⟨vHat, hvHat, hvHatcc⟩ := hsB3 uHat huHatZ
    refine ⟨Work.WilE7.takeZ hm vHat, Finset.mem_image.mpr ⟨vHat, hvHat, rfl⟩, ?_⟩
    have hvHatmem : vHat ∈ connectedComponentIn
        (Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g)) uHat := by
      rw [hvHatcc]
      exact mem_connectedComponentIn (hsB1 hvHat)
    have hsub : connectedComponentIn (Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g)) uHat ⊆
        Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g) :=
      connectedComponentIn_subset _ _
    have himg : Work.WilE7.takeZ hm '' connectedComponentIn
        (Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g)) uHat ⊆ cubeC k ∩ Zset c g := by
      rintro y ⟨z, hz, rfl⟩
      exact takeZ_mem_of_mem_extFam_Zset hm (hsub hz)
    have hpre : IsPreconnected (Work.WilE7.takeZ hm '' connectedComponentIn
        (Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g)) uHat) :=
      isPreconnected_connectedComponentIn.image _ (continuous_takeZ hm).continuousOn
    have hxmem : x ∈ Work.WilE7.takeZ hm '' connectedComponentIn
        (Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g)) uHat :=
      ⟨uHat, mem_connectedComponentIn huHatZ, by rw [huHat]; exact takeZ_append hm x t⟩
    exact hpre.subset_connectedComponentIn hxmem himg ⟨vHat, hvHatmem, rfl⟩

/-- **The ball statement implies `interior_hits`.**  The hypothesis is exactly the statement of
`Work.WilE2.euclidean_ball_components` (GV Corollary 3.3). -/
theorem interior_hits_of_ball
    (hBall : ∀ (F : ℕ), ∃ p : Polynomial ℕ,
      ∀ (n r : ℕ) (c : EAChain n r) (g : Finset (EAPoly n r)) (R : ℝ), n + r ≤ F →
        ∃ s : Finset (Fin n → ℝ),
          (↑s : Set (Fin n → ℝ)) ⊆ Zset c g ∩ {x | ∑ i, (x i) ^ 2 ≤ R ^ 2} ∧
          s.card ≤ p.eval (∑ f ∈ g, atomDeg f) ∧
          Hits (Zset c g ∩ {x | ∑ i, (x i) ^ 2 ≤ R ^ 2}) s)
    (F : ℕ) :
    ∃ p : Polynomial ℕ,
      ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r) (g : Finset (WilkiesDesign.E.EAPoly k r)),
        k + r ≤ F → ∃ s : Finset (Fin k → ℝ),
          (↑s : Set (Fin k → ℝ)) ⊆ WilkiesDesign.E.cubeC k ∩ Work.WilE2.Zset c g ∧
          s.card ≤ p.eval (∑ f ∈ g, WilkiesDesign.E.atomDeg f) ∧
          (∀ x ∈ WilkiesDesign.E.cubeC k ∩ Work.WilE2.Zset c g ∩
              interior (WilkiesDesign.E.cubeC k),
            ∃ y ∈ s, y ∈ connectedComponentIn
              (WilkiesDesign.E.cubeC k ∩ Work.WilE2.Zset c g) x) := by
  obtain ⟨pBall, hpBall⟩ := hBall (3 * F)
  refine ⟨pBall.comp ((Polynomial.X + Polynomial.C (F : ℕ)) *
      (Polynomial.X + Polynomial.C 3)), ?_⟩
  intro k r c g hkr
  have hkF : k ≤ F := by omega
  have hm : k ≤ k + k := by omega
  have hfmt : (k + k) + r ≤ 3 * F := by omega
  obtain ⟨sB, hsB1, hsB2, hsB3⟩ :=
    hpBall (k + k) r (Work.WilE7.EAChain.pad hm c) (extFam hm g) (Real.sqrt k) hfmt
  refine ⟨sB.image (Work.WilE7.takeZ hm), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨yHat, hyHat, rfl⟩ := Finset.mem_image.mp hy
    exact takeZ_mem_of_mem_extFam_Zset hm (hsB1 hyHat).1
  · calc (sB.image (Work.WilE7.takeZ hm)).card ≤ sB.card := Finset.card_image_le
      _ ≤ pBall.eval (∑ Q ∈ extFam hm g, atomDeg Q) := hsB2
      _ ≤ pBall.eval (((Polynomial.X + Polynomial.C (F : ℕ)) *
            (Polynomial.X + Polynomial.C 3)).eval (∑ f ∈ g, atomDeg f)) :=
          Work.WilE5.Cells.khovEval_mono (sum_atomDeg_extFam_le hm hkF g)
      _ = (pBall.comp ((Polynomial.X + Polynomial.C (F : ℕ)) *
            (Polynomial.X + Polynomial.C 3))).eval (∑ f ∈ g, atomDeg f) :=
          (Polynomial.eval_comp (p := pBall)
            (q := (Polynomial.X + Polynomial.C (F : ℕ)) * (Polynomial.X + Polynomial.C 3))
            (x := ∑ f ∈ g, atomDeg f)).symm
  · intro x hx
    obtain ⟨⟨hxc, hxz⟩, _⟩ := hx
    set t : Fin k → ℝ := fun i => Real.sqrt (1 - (x i) ^ 2) with ht
    have ht_sq : ∀ i, (t i) ^ 2 = 1 - (x i) ^ 2 := by
      intro i
      rw [ht]
      refine Real.sq_sqrt ?_
      have h := abs_le.mp (hxc i)
      nlinarith [h.1, h.2]
    set ũ : Fin (k + k) → ℝ := Fin.append x t with hũ
    have hũZ : ũ ∈ Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g) := by
      rw [mem_extFam_Zset hm c g ũ]
      refine ⟨?_, ?_⟩
      · intro f hf
        rw [hũ, takeZ_append hm x t]
        exact hxz f hf
      · intro i
        have h1 : ũ (Fin.castLE hm i) = x i := by
          rw [hũ]
          have h : (Fin.castLE hm i : Fin (k + k)) = Fin.castAdd k i := Fin.ext rfl
          rw [h, Fin.append_left]
        have h2 : ũ (Fin.natAdd k i) = t i := by
          rw [hũ]; exact Fin.append_right x t i
        rw [h1, h2, ht_sq i]
        ring
    obtain ⟨vHat, hvHat, hvHatcc⟩ := hsB3 ũ ⟨hũZ, extFam_Zset_subset_ball hm c g hũZ⟩
    refine ⟨Work.WilE7.takeZ hm vHat, Finset.mem_image.mpr ⟨vHat, hvHat, rfl⟩, ?_⟩
    have hvHatmem : vHat ∈ connectedComponentIn
        (Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g)) ũ := by
      rw [← extFam_Zset_inter_ball hm c g, hvHatcc]
      exact mem_connectedComponentIn (hsB1 hvHat)
    have hsub : connectedComponentIn (Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g)) ũ ⊆
        Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g) :=
      connectedComponentIn_subset _ _
    have himg : Work.WilE7.takeZ hm '' connectedComponentIn
        (Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g)) ũ ⊆ cubeC k ∩ Zset c g := by
      rintro y ⟨z, hz, rfl⟩
      exact takeZ_mem_of_mem_extFam_Zset hm (hsub hz)
    have hpre : IsPreconnected (Work.WilE7.takeZ hm '' connectedComponentIn
        (Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g)) ũ) :=
      isPreconnected_connectedComponentIn.image _ (continuous_takeZ hm).continuousOn
    have hxmem : x ∈ Work.WilE7.takeZ hm '' connectedComponentIn
        (Zset (Work.WilE7.EAChain.pad hm c) (extFam hm g)) ũ :=
      ⟨ũ, mem_connectedComponentIn hũZ, by rw [hũ]; exact takeZ_append hm x t⟩
    exact hpre.subset_connectedComponentIn hxmem himg ⟨vHat, hvHatmem, rfl⟩

theorem interior_hits (hE2a : Work.WilE2.KhoBound) (hSard : Work.WilE2.SardDense) (F : ℕ) :
    ∃ p : Polynomial ℕ, ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r) (g : Finset (WilkiesDesign.E.EAPoly k r)),
      k + r ≤ F → ∃ s : Finset (Fin k → ℝ),
        (↑s : Set (Fin k → ℝ)) ⊆ WilkiesDesign.E.cubeC k ∩ Work.WilE2.Zset c g ∧
        s.card ≤ p.eval (∑ f ∈ g, WilkiesDesign.E.atomDeg f) ∧
        (∀ x ∈ WilkiesDesign.E.cubeC k ∩ Work.WilE2.Zset c g ∩ interior (WilkiesDesign.E.cubeC k),
          ∃ y ∈ s, y ∈ connectedComponentIn (WilkiesDesign.E.cubeC k ∩ Work.WilE2.Zset c g) x) :=
  interior_hits_of_ball (fun F => Work.WilE2.Cb.ball_components hE2a hSard F) F

end Work.WilE2
