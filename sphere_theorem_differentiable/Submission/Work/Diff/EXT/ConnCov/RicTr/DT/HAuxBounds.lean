import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.HAuxKernel
import Submission.Work.Diff.EXT.covKAExt_tensorial

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.Diff.EXT.ConnCov.DT

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- **The aOf-tower bound on arbitrary smooth fields.**  The `ValBound` hypothesis (stated on the
`Classical.epsilon`-chosen smooth extensions `smoothExt`) transfers to arbitrary smooth fields by
value dependence of `covKAExt` (`covKAExt_tensorial`). -/
theorem aOfTower_val_bound (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (j : ℕ) (b : ℝ)
    (h : ValBound G t j (tower (lcOf (G 0)) (fun _ => aOf G t) j) b)
    (x : M) (v : Fin j → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
    (hv : ∀ p, SmE I M (v p)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) :
    |tower (lcOf (G 0)) (fun _ => aOf G t) j v A B C x|
      ≤ b * (Finset.univ.prod (fun p : Fin j =>
            Real.sqrt ((G t).inner x (v p x) (v p x))))
          * Real.sqrt ((G t).inner x (A x) (A x))
          * Real.sqrt ((G t).inner x (B x) (B x))
          * Real.sqrt ((G t).inner x (C x) (C x)) := by
  have hT := valOp_tower_eq_covKAExt (I := I) (M := M) G t j x
    (fun p => v p x) (A x) (B x) (C x)
  have hv' : ∀ p : Fin j, Work.Diff.GE.SmoothFieldT (I := I) (M := M)
      (Submission.Diff.smoothExt x (v p x)) :=
    fun p => Work.Diff.GE.smoothExt_cmdiff x (v p x)
  have hA' : Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Submission.Diff.smoothExt x (A x)) :=
    Work.Diff.GE.smoothExt_cmdiff x (A x)
  have hB' : Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Submission.Diff.smoothExt x (B x)) :=
    Work.Diff.GE.smoothExt_cmdiff x (B x)
  have hC' : Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Submission.Diff.smoothExt x (C x)) :=
    Work.Diff.GE.smoothExt_cmdiff x (C x)
  have hval := Work.Diff.EXT.covKAExt_tensorial (I := I) (M := M) hLC G t j x
    (fun p => Submission.Diff.smoothExt x (v p x)) v
    (Submission.Diff.smoothExt x (A x)) A (Submission.Diff.smoothExt x (B x)) B
    (Submission.Diff.smoothExt x (C x)) C
    hv' hv hA' hA hB' hB hC' hC
    (fun p : Fin j => Work.Diff.GE.smoothExt_apply x (v p x))
    (Work.Diff.GE.smoothExt_apply x (A x)) (Work.Diff.GE.smoothExt_apply x (B x))
    (Work.Diff.GE.smoothExt_apply x (C x))
  rw [tower_eq_covKAExt]
  rw [← hval]
  rw [← hT]
  exact h x (fun p => v p x) (A x) (B x) (C x)

/-- Positivity of the metric pairing on a square. -/
theorem inner_self_nonneg (g : Submission.Diff.SMet I M) (x : M)
    (v : TangentSpace I x) : 0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with h | h
  · subst h; simp
  · exact le_of_lt (g.pos x v h)

/-- **The bound of the metric tower from the bound of the `aOf`-tower.**  For `i ≥ 1`, the `i`-th
covariant derivative of `g_t` is the sum of the two slot-permutations of the `(i-1)`-st derivative
of `aOf` (`gtTower_succ_eq_swap`), so its bound follows from the hypothesis `hA` at level `i-1`. -/
theorem gtTower_val_bound (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (x : M) (m : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ (d : Fin m → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ p, SmE I M (d p)) → SmE I M A → SmE I M B → SmE I M C →
      |tower (lcOf (G 0)) (fun _ => aOf G t) m d A B C x|
        ≤ b * (Finset.univ.prod (fun p : Fin m =>
              Real.sqrt ((G t).inner x (d p x) (d p x))))
            * Real.sqrt ((G t).inner x (A x) (A x))
            * Real.sqrt ((G t).inner x (B x) (B x))
            * Real.sqrt ((G t).inner x (C x) (C x)))
    (d : Fin (m + 1) → TF (I := I) (M := M)) (Y Z : TF (I := I) (M := M))
    (hd : ∀ p, SmE I M (d p)) (hY : SmE I M Y) (hZ : SmE I M Z) :
    |gtTower G t (m + 1) d Y Z x|
      ≤ 2 * b * (Finset.univ.prod (fun p : Fin (m + 1) =>
            Real.sqrt ((G t).inner x (d p x) (d p x))))
          * Real.sqrt ((G t).inner x (Y x) (Y x))
          * Real.sqrt ((G t).inner x (Z x) (Z x)) := by
  have hkey : gtTower G t (m + 1) d Y Z x
      = tower (lcOf (G 0)) (fun _ => aOf G t) m
            (fun p : Fin m => d (Fin.castSucc p)) (d (Fin.last m)) Y Z x
        + tower (lcOf (G 0)) (fun _ => aOf G t) m
            (fun p : Fin m => d (Fin.castSucc p)) (d (Fin.last m)) Z Y x :=
    gtTower_succ_eq_swap hLC G t m d Y Z hd hY hZ x
  have hdc : ∀ p : Fin m, SmE I M ((fun p : Fin m => d (Fin.castSucc p)) p) :=
    fun p => hd (Fin.castSucc p)
  have h1 := h (fun p : Fin m => d (Fin.castSucc p)) (d (Fin.last m)) Y Z hdc
    (hd (Fin.last m)) hY hZ
  have h2 := h (fun p : Fin m => d (Fin.castSucc p)) (d (Fin.last m)) Z Y hdc
    (hd (Fin.last m)) hZ hY
  have hprod : (∏ p : Fin (m + 1), Real.sqrt ((G t).inner x (d p x) (d p x)))
      = (∏ p : Fin m, Real.sqrt ((G t).inner x (d (Fin.castSucc p) x)
            (d (Fin.castSucc p) x)))
        * Real.sqrt ((G t).inner x (d (Fin.last m) x) (d (Fin.last m) x)) :=
    Fin.prod_univ_castSucc (f := fun p : Fin (m + 1) =>
      Real.sqrt ((G t).inner x (d p x) (d p x)))
  rw [hkey, hprod]
  set P := ∏ p : Fin m, Real.sqrt ((G t).inner x (d (Fin.castSucc p) x)
      (d (Fin.castSucc p) x)) with hPdef
  set q := Real.sqrt ((G t).inner x (d (Fin.last m) x) (d (Fin.last m) x)) with hqdef
  set sY := Real.sqrt ((G t).inner x (Y x) (Y x)) with hYdef
  set sZ := Real.sqrt ((G t).inner x (Z x) (Z x)) with hZdef
  have h1' : |tower (lcOf (G 0)) (fun _ => aOf G t) m
        (fun p : Fin m => d (Fin.castSucc p)) (d (Fin.last m)) Y Z x|
      ≤ ((b * P) * q) * sY * sZ := by
    simpa only [hPdef, hqdef, hYdef, hZdef, mul_assoc] using h1
  have h2' : |tower (lcOf (G 0)) (fun _ => aOf G t) m
        (fun p : Fin m => d (Fin.castSucc p)) (d (Fin.last m)) Z Y x|
      ≤ ((b * P) * q) * sZ * sY := by
    simpa only [hPdef, hqdef, hYdef, hZdef, mul_assoc] using h2
  have key : (((b * P) * q) * sY) * sZ + (((b * P) * q) * sZ) * sY
      ≤ (((2 * b) * (P * q)) * sY) * sZ := by
    have e1 : (((b * P) * q) * sZ) * sY = (((b * P) * q) * sY) * sZ := by ring
    have e2 : (((2 * b) * (P * q)) * sY) * sZ = 2 * ((((b * P) * q) * sY) * sZ) := by ring
    rw [e1, e2]
    linarith
  refine le_trans (abs_add_le _ _) ?_
  calc |tower (lcOf (G 0)) (fun _ => aOf G t) m
          (fun p : Fin m => d (Fin.castSucc p)) (d (Fin.last m)) Y Z x|
        + |tower (lcOf (G 0)) (fun _ => aOf G t) m
          (fun p : Fin m => d (Fin.castSucc p)) (d (Fin.last m)) Z Y x|
      ≤ ((b * P) * q) * sY * sZ + ((b * P) * q) * sZ * sY := add_le_add h1' h2'
    _ ≤ (((2 * b) * (P * q)) * sY) * sZ := key

/-- **The bound of an expansion term.**  The metric factor has level `i ≥ 1` (so the `aOf`-tower
hypothesis at level `i - 1` applies), the δ factor has level `j`, and the two selections are
injective with disjoint images; the product of the `i + j` norm factors is then dominated by the
full product over the `c = i + j` directions (`Finset.prod_le_prod₀`, `Finset.prod_image`,
`Finset.prod_union`, `Finset.prod_le_prod_of_subset_of_one_le`). -/
theorem selTerm_val_bound (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (x : M) {c i j : ℕ} (hc : i + j = c)
    (hi : 1 ≤ i) (F : Fin i → Fin c) (G' : Fin j → Fin c)
    (hf : Function.Injective F) (hg : Function.Injective G')
    (hdisj : Disjoint (Set.range F) (Set.range G'))
    (hcov : ∀ k : Fin c, k ∈ Set.range F ∪ Set.range G')
    (S DT : ℝ) (hS : 0 ≤ S) (hDT : 0 ≤ DT)
    (hbS : ∀ (d : Fin i → TF (I := I) (M := M)) (Y Z : TF (I := I) (M := M)),
      (∀ p, SmE I M (d p)) → SmE I M Y → SmE I M Z →
      |gtTower G t i d Y Z x|
        ≤ S * (Finset.univ.prod (fun p : Fin i =>
              Real.sqrt ((G t).inner x (d p x) (d p x))))
            * Real.sqrt ((G t).inner x (Y x) (Y x))
            * Real.sqrt ((G t).inner x (Z x) (Z x)))
    (hbT : ∀ (d : Fin j → TF (I := I) (M := M)) (Y X : TF (I := I) (M := M)),
      (∀ p, SmE I M (d p)) → SmE I M Y → SmE I M X →
      Real.sqrt ((G t).inner x (deltaTower G t j d Y X x) (deltaTower G t j d Y X x))
        ≤ DT * (Finset.univ.prod (fun p : Fin j =>
              (1 + Real.sqrt ((G t).inner x (d p x) (d p x)))))
            * Real.sqrt ((G t).inner x (Y x) (Y x))
            * Real.sqrt ((G t).inner x (X x) (X x)))
    (v : Fin c → TF (I := I) (M := M)) (X Y Z : TF (I := I) (M := M))
    (hv : ∀ k, SmE I M (v k)) (hX : SmE I M X) (hY : SmE I M Y) (hZ : SmE I M Z) :
    |selTerm G t c i j F G' v X Y Z x|
      ≤ S * DT * ((Finset.univ.prod (fun k : Fin c =>
            (1 + Real.sqrt ((G t).inner x (v k x) (v k x)))))
          * Real.sqrt ((G t).inner x (X x) (X x))
          * Real.sqrt ((G t).inner x (Y x) (Y x))
          * Real.sqrt ((G t).inner x (Z x) (Z x))) := by
  have hdF : ∀ p : Fin i, SmE I M ((fun k => v (F k)) p) := fun p => hv (F p)
  have hdG : ∀ p : Fin j, SmE I M ((fun k => v (G' k)) p) := fun p => hv (G' p)
  have hW : SmE I M (deltaTower G t j (fun k => v (G' k)) Y X) :=
    deltaTower_sm hLC G t j _ Y X hdG hY hX
  have h1 := hbS (fun k => v (F k)) (deltaTower G t j (fun k => v (G' k)) Y X) Z hdF hW hZ
  have h2 := hbT (fun k => v (G' k)) Y X hdG hY hX
  -- abbreviations so that all products keep one shape
  set af : Fin c → ℝ := fun k => Real.sqrt ((G t).inner x (v k x) (v k x)) with hafdef
  set P1 : ℝ := Finset.univ.prod (fun p : Fin i => af (F p)) with hP1def
  set P2 : ℝ := Finset.univ.prod (fun p : Fin j => (1 + af (G' p))) with hP2def
  set Pg : ℝ := Finset.univ.prod (fun k : Fin c => (1 + af k)) with hPgdef
  set sW : ℝ := Real.sqrt ((G t).inner x (deltaTower G t j (fun k => v (G' k)) Y X x)
      (deltaTower G t j (fun k => v (G' k)) Y X x)) with hsWdef
  set sX : ℝ := Real.sqrt ((G t).inner x (X x) (X x)) with hsXdef
  set sY : ℝ := Real.sqrt ((G t).inner x (Y x) (Y x)) with hsYdef
  set sZ : ℝ := Real.sqrt ((G t).inner x (Z x) (Z x)) with hsZdef
  have haf0 : ∀ k, 0 ≤ af k := fun k => Real.sqrt_nonneg _
  have hP10 : 0 ≤ P1 := Finset.prod_nonneg (fun p _ => haf0 (F p))
  have hP20 : 0 ≤ P2 := Finset.prod_nonneg (fun p _ => by linarith [haf0 (G' p)])
  have hPg0 : 0 ≤ Pg := Finset.prod_nonneg (fun k _ => by linarith [haf0 k])
  have hsW0 : 0 ≤ sW := Real.sqrt_nonneg _
  have hsX0 : 0 ≤ sX := Real.sqrt_nonneg _
  have hsY0 : 0 ≤ sY := Real.sqrt_nonneg _
  have hsZ0 : 0 ≤ sZ := Real.sqrt_nonneg _
  -- (1) the pointwise product domination
  have hprod : P1 * P2 ≤ Pg := by
    have hstep : P1 ≤ Finset.univ.prod (fun p : Fin i => (1 + af (F p))) := by
      rw [hP1def]
      exact Finset.prod_le_prod₀ (s := Finset.univ) (fun p _ => haf0 (F p))
        (fun p _ => by linarith [haf0 (F p)])
    have hF : (Finset.univ.prod (fun p : Fin i => (1 + af (F p))))
        = (Finset.univ.image F).prod (fun k => (1 + af k)) := by
      rw [← Finset.prod_image (f := fun k : Fin c => (1 + af k))
        (s := (Finset.univ : Finset (Fin i))) (g := F) (fun a _ b _ hab => hf hab)]
    have hG : (Finset.univ.prod (fun p : Fin j => (1 + af (G' p))))
        = (Finset.univ.image G').prod (fun k => (1 + af k)) := by
      rw [← Finset.prod_image (f := fun k : Fin c => (1 + af k))
        (s := (Finset.univ : Finset (Fin j))) (g := G') (fun a _ b _ hab => hg hab)]
    have hdisj' : Disjoint (Finset.univ.image F) (Finset.univ.image G') := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      rw [Finset.mem_image] at hk hk'
      obtain ⟨a, _, ha⟩ := hk
      obtain ⟨b, _, hb⟩ := hk'
      exact Set.disjoint_left.mp hdisj (Set.mem_range.mpr ⟨a, ha⟩) (Set.mem_range.mpr ⟨b, hb⟩)
    have hunion : (Finset.univ.image F ∪ Finset.univ.image G').prod (fun k => (1 + af k))
        = (Finset.univ.image F).prod (fun k => (1 + af k))
          * (Finset.univ.image G').prod (fun k => (1 + af k)) :=
      Finset.prod_union hdisj'
    have huniv : Finset.univ.image F ∪ Finset.univ.image G' = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro k
      rcases hcov k with h | h
      · obtain ⟨p, hp⟩ := Set.mem_range.mp h
        rw [Finset.mem_union]
        exact Or.inl (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hp⟩)
      · obtain ⟨p, hp⟩ := Set.mem_range.mp h
        rw [Finset.mem_union]
        exact Or.inr (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hp⟩)
    have hsub : (Finset.univ.image F ∪ Finset.univ.image G').prod (fun k => (1 + af k))
        ≤ Pg := by
      rw [huniv, hPgdef]
    calc P1 * P2 = P1 * (Finset.univ.prod (fun p : Fin j => (1 + af (G' p)))) := by rw [hP2def]
      _ ≤ (Finset.univ.prod (fun p : Fin i => (1 + af (F p))))
            * (Finset.univ.prod (fun p : Fin j => (1 + af (G' p)))) :=
          mul_le_mul_of_nonneg_right hstep hP20
      _ = (Finset.univ.image F).prod (fun k => (1 + af k))
            * (Finset.univ.image G').prod (fun k => (1 + af k)) := by rw [hF, hG]
      _ = (Finset.univ.image F ∪ Finset.univ.image G').prod (fun k => (1 + af k)) := by
          rw [hunion]
      _ ≤ Pg := hsub
  -- (2) `h1`, `h2` in abbreviated form
  have h1' : |gtTower G t i (fun k => v (F k))
        (deltaTower G t j (fun k => v (G' k)) Y X) Z x| ≤ ((S * P1) * sW) * sZ := by
    simpa only [hP1def, hsWdef, hsZdef, mul_assoc] using h1
  have h2' : sW ≤ ((DT * P2) * sY) * sX := by
    simpa only [hP2def, hsWdef, hsXdef, hsYdef, mul_assoc] using h2
  simp only [selTerm]
  show |gtTower G t i (fun k => v (F k)) (deltaTower G t j (fun k => v (G' k)) Y X) Z x|
      ≤ S * DT * (Pg * sX * sY * sZ)
  calc |gtTower G t i (fun k => v (F k)) (deltaTower G t j (fun k => v (G' k)) Y X) Z x|
      ≤ ((S * P1) * sW) * sZ := h1'
    _ ≤ ((S * P1) * (((DT * P2) * sY) * sX)) * sZ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2' (mul_nonneg hS hP10)) hsZ0
    _ = ((S * DT * (P1 * P2)) * sY * sX) * sZ := by ring
    _ ≤ ((S * DT * Pg) * sY * sX) * sZ := by
        have hSD : S * DT * (P1 * P2) ≤ S * DT * Pg :=
          mul_le_mul_of_nonneg_left hprod (mul_nonneg hS hDT)
        have e1 : (S * DT * (P1 * P2)) * sY ≤ (S * DT * Pg) * sY :=
          mul_le_mul_of_nonneg_right hSD hsY0
        have e2 : ((S * DT * (P1 * P2)) * sY) * sX ≤ ((S * DT * Pg) * sY) * sX :=
          mul_le_mul_of_nonneg_right e1 hsX0
        have e3 : (((S * DT * (P1 * P2)) * sY) * sX) * sZ
            ≤ (((S * DT * Pg) * sY) * sX) * sZ :=
          mul_le_mul_of_nonneg_right e2 hsZ0
        calc ((S * DT * (P1 * P2)) * sY * sX) * sZ
            = (((S * DT * (P1 * P2)) * sY) * sX) * sZ := by ring
          _ ≤ (((S * DT * Pg) * sY) * sX) * sZ := e3
          _ = ((S * DT * Pg) * sY * sX) * sZ := by ring
    _ = S * DT * (Pg * sX * sY * sZ) := by ring

/-- **From a pairing bound to a norm bound** (the Riesz/Cauchy–Schwarz step). -/
theorem sqrt_inner_le_of_pairing_le (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (x : M)
    (W : TangentSpace I x) (K : ℝ) (hK : 0 ≤ K) (h : ∀ Z : TangentSpace I x,
      |(G t).inner x W Z| ≤ K * Real.sqrt ((G t).inner x Z Z)) :
    Real.sqrt ((G t).inner x W W) ≤ K := by
  have hWW := h W
  have h0 : 0 ≤ Real.sqrt ((G t).inner x W W) := Real.sqrt_nonneg _
  have hs : Real.sqrt ((G t).inner x W W) * Real.sqrt ((G t).inner x W W)
      = (G t).inner x W W := Real.mul_self_sqrt (inner_self_nonneg (G t) x W)
  rw [abs_of_nonneg (inner_self_nonneg (G t) x W)] at hWW
  have hWW' : Real.sqrt ((G t).inner x W W) * Real.sqrt ((G t).inner x W W)
      ≤ K * Real.sqrt ((G t).inner x W W) := by
    rw [hs]; exact hWW
  rcases eq_or_lt_of_le h0 with hz | hpos
  · rw [← hz]; exact hK
  · exact le_of_mul_le_mul_right hWW' hpos

end Work.Diff.EXT.ConnCov.DT
