import Mathlib
import Submission.Work.Diff.EXT.evolX.compLadderDefs
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.evolX.pairingSplitNB
import Submission.Work.Diff.EXT.evolX.ladderPlumb
import Submission.Work.Diff.GE.dRicPhi_eq_sum_covRm
import Submission.Work.EXT.sum_inner_smul_eq_self_of_isONFrame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The jets of the pairing operator `pairVec g U`

The target `Work.Diff.EXT.evolX.pairVecJetAll` identifies the `c`-th packed jet of the pairing
operator `pairVec g U : F ↦ ⟪U (F ∘ castSucc), F (last)⟫` (arity `K+1`) with the metric pairing of
the `c`-fold covariant derivative `dvc g K U c` (arity `K+c`) on the first `K+c` entries of the
tuple with the *last* entry of the tuple.

The proof is the induction on `c`.  At the step, `extStep` differentiates `Av c := ⟪dvc^c (·), ·⟫`;
the Leibniz rule for the pairing (`Work.Diff.EXT.evolX.pairingSplitNB`, which needs the
differentiability of the field `dvc^c (firstPart ·)`) produces a term that cancels against the
correction term of `extStep` in the *last* slot, and the remaining `K+c` correction terms are exactly
the recursion `dvStep` of `dvc`.  The differentiability of `dvc g K U c T` (for smooth tuples `T`) is
itself a consequence of the identity at level `c` together with the `JetSmoothOp` hypothesis of the
target: it is recovered from the pairings with a *globally smooth* orthonormal frame near the base
point (`Work.Diff.GE.exists_smooth_onframe` + `mdiffAtOfPairings`).
-/

set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Work.Diff.EXT.evolX

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

section Aux

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The positional bookkeeping -/

/-- The embedding of `Fin (K+c)` into the positions of a `((K+1)+c)`-tuple that omits the last
position. -/
def emb (K c : ℕ) : Fin (K + c) → Fin ((K + 1) + c) :=
  Fin.cast (Nat.succ_add K c).symm ∘ Fin.castSucc

/-- The last position of a `((K+1)+c)`-tuple. -/
def embL (K c : ℕ) : Fin ((K + 1) + c) :=
  Fin.cast (Nat.succ_add K c).symm (Fin.last (K + c))

theorem emb_injective (K c : ℕ) : Function.Injective (emb K c) :=
  (Fin.cast_injective (Nat.succ_add K c).symm).comp (Fin.castSucc_injective (K + c))

theorem emb_ne_embL (K c : ℕ) (r : Fin (K + c)) : emb K c r ≠ embL K c := by
  intro h
  have h2 : Fin.castSucc r = Fin.last (K + c) :=
    Fin.cast_injective (Nat.succ_add K c).symm h
  exact Fin.castSucc_ne_last r h2

/-- A property that holds eventually at `x` holds eventually at every point of a neighbourhood of
`x`. -/
theorem eventually_nhds_of_eventually {P : M → Prop} {x : M} (h : ∀ᶠ z in 𝓝 x, P z) :
    ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, P z := by
  obtain ⟨U, hU, hsub⟩ := Filter.eventually_iff_exists_mem.mp h
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hU
  filter_upwards [hVopen.mem_nhds hxV] with y hyV
  exact Filter.mem_of_superset (hVopen.mem_nhds hyV) (hVsub.trans hsub)

/-- **The sum over a `((K+1)+c)`-tuple splits at its last position.** -/
theorem sum_emb {K c : ℕ} (f : Fin ((K + 1) + c) → ℝ) :
    (∑ s, f s) = (∑ r : Fin (K + c), f (emb K c r)) + f (embL K c) := by
  rw [show (∑ s : Fin ((K + 1) + c), f s)
      = ∑ t : Fin (K + c + 1), f (Fin.cast (Nat.succ_add K c).symm t) from
    Fintype.sum_bijective (finCongr (Nat.succ_add K c)) (finCongr _).bijective f
      (fun t : Fin (K + c + 1) => f (Fin.cast (Nat.succ_add K c).symm t))
      (fun s => by rw [finCongr_apply]; exact congrArg f (Fin.ext rfl))]
  rw [Fin.sum_univ_castSucc]
  rfl

/-! ## The interaction with `firstPart` and `lastPart` -/

theorem firstPart_eq (K c : ℕ) (G : Fin ((K + 1) + c) → Work.Diff.EXT.TField (I := I) (M := M)) :
    firstPart (I := I) (M := M) G = G ∘ emb K c := by
  funext i
  exact congrArg G (Fin.ext rfl)

theorem lastPart_eq (K c : ℕ) (G : Fin ((K + 1) + c) → Work.Diff.EXT.TField (I := I) (M := M)) :
    lastPart (I := I) (M := M) G = G (embL K c) :=
  congrArg G (Fin.ext rfl)

theorem arg_eq_emb (K c : ℕ) (G : Fin ((K + 1) + c) → Work.Diff.EXT.TField (I := I) (M := M))
    (r : Fin (K + c)) :
    G (emb K c r) = firstPart (I := I) (M := M) G r := by
  rw [firstPart_eq]
  rfl

theorem arg_eq_embL (K c : ℕ) (G : Fin ((K + 1) + c) → Work.Diff.EXT.TField (I := I) (M := M)) :
    G (embL K c) = lastPart (I := I) (M := M) G :=
  (lastPart_eq K c G).symm

theorem firstPart_update_emb (K c : ℕ)
    (G : Fin ((K + 1) + c) → Work.Diff.EXT.TField (I := I) (M := M)) (r : Fin (K + c))
    (X : Work.Diff.EXT.TField (I := I) (M := M)) :
    firstPart (I := I) (M := M) (Function.update G (emb K c r) X)
      = Function.update (firstPart (I := I) (M := M) G) r X := by
  rw [firstPart_eq K c, Function.update_comp_eq_of_injective G (emb_injective K c) r X,
    ← firstPart_eq (K := K) (c := c)]

theorem lastPart_update_emb (K c : ℕ)
    (G : Fin ((K + 1) + c) → Work.Diff.EXT.TField (I := I) (M := M)) (r : Fin (K + c))
    (X : Work.Diff.EXT.TField (I := I) (M := M)) :
    lastPart (I := I) (M := M) (Function.update G (emb K c r) X)
      = lastPart (I := I) (M := M) G := by
  rw [lastPart_eq K c, lastPart_eq K c, Function.update_apply,
    if_neg (Ne.symm (emb_ne_embL K c r))]

theorem firstPart_update_embL (K c : ℕ)
    (G : Fin ((K + 1) + c) → Work.Diff.EXT.TField (I := I) (M := M))
    (X : Work.Diff.EXT.TField (I := I) (M := M)) :
    firstPart (I := I) (M := M) (Function.update G (embL K c) X)
      = firstPart (I := I) (M := M) G := by
  funext i
  rw [firstPart_eq K c, firstPart_eq K c]
  exact Function.update_of_ne (emb_ne_embL K c i) X G

theorem lastPart_update_embL (K c : ℕ)
    (G : Fin ((K + 1) + c) → Work.Diff.EXT.TField (I := I) (M := M))
    (X : Work.Diff.EXT.TField (I := I) (M := M)) :
    lastPart (I := I) (M := M) (Function.update G (embL K c) X) = X := by
  rw [lastPart_eq, Function.update_self]

/-! ## The `succ`-shift of a `((K+1)+(c+1))`-tuple -/

theorem firstPart_comp_succ (K c : ℕ)
    (F : Fin ((K + 1) + (c + 1)) → Work.Diff.EXT.TField (I := I) (M := M)) :
    firstPart (I := I) (M := M) (fun i : Fin ((K + 1) + c) => F i.succ)
      = fun i : Fin (K + c) => (firstPart (I := I) (M := M) F) i.succ := by
  funext i
  rw [firstPart_eq K c, firstPart_eq (K := K) (c := c + 1)]
  exact congrArg F (Fin.ext rfl)

theorem lastPart_comp_succ (K c : ℕ)
    (F : Fin ((K + 1) + (c + 1)) → Work.Diff.EXT.TField (I := I) (M := M)) :
    lastPart (I := I) (M := M) (fun i : Fin ((K + 1) + c) => F i.succ)
      = lastPart (I := I) (M := M) F := by
  rw [lastPart_eq K c, lastPart_eq (K := K) (c := c + 1)]
  exact congrArg F (Fin.ext rfl)

theorem firstPart_zero (K c : ℕ)
    (F : Fin ((K + 1) + (c + 1)) → Work.Diff.EXT.TField (I := I) (M := M)) :
    (firstPart (I := I) (M := M) F) (0 : Fin (K + (c + 1))) = F 0 := by
  rw [firstPart_eq (K := K) (c := c + 1)]
  exact congrArg F (Fin.ext rfl)

/-! ## The extension of a tuple by a last entry -/

/-- The `((K+1)+c)`-tuple whose first `K+c` entries are those of `T` and whose last entry is `D`. -/
noncomputable def extTup (K c : ℕ) (T : Fin (K + c) → Work.Diff.EXT.TField (I := I) (M := M))
    (D : Work.Diff.EXT.TField (I := I) (M := M)) :
    Fin ((K + 1) + c) → Work.Diff.EXT.TField (I := I) (M := M) :=
  fun j => if h : (j : ℕ) < K + c then T ⟨(j : ℕ), h⟩ else D

theorem firstPart_extTup {K c : ℕ} (T : Fin (K + c) → Work.Diff.EXT.TField (I := I) (M := M))
    (D : Work.Diff.EXT.TField (I := I) (M := M)) :
    firstPart (I := I) (M := M) (extTup K c T D) = T := by
  funext i
  have h : ((Fin.castLE (by omega : K + c ≤ (K + 1) + c) i : Fin ((K + 1) + c)) : ℕ) < K + c :=
    i.isLt
  simp only [firstPart, extTup, h, dif_pos]
  exact congrArg T (Fin.ext rfl)

theorem lastPart_extTup {K c : ℕ} (T : Fin (K + c) → Work.Diff.EXT.TField (I := I) (M := M))
    (D : Work.Diff.EXT.TField (I := I) (M := M)) :
    lastPart (I := I) (M := M) (extTup K c T D) = D := by
  have h : ((embL K c : Fin ((K + 1) + c)) : ℕ) = K + c := rfl
  rw [lastPart_eq K c, extTup]
  simp only [h, lt_self_iff_false, not_false_eq_true, dif_neg]

theorem smoothF_extTup {K c : ℕ} {T : Fin (K + c) → Work.Diff.EXT.TField (I := I) (M := M)}
    {D : Work.Diff.EXT.TField (I := I) (M := M)}
    (hT : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (T i))
    (hD : Work.Diff.EXT.SmoothF (I := I) (M := M) D) :
    ∀ j, Work.Diff.EXT.SmoothF (I := I) (M := M) (extTup K c T D j) := by
  intro j
  simp only [extTup]
  split_ifs with h
  · exact hT _
  · exact hD

/-! ## The right-hand side operator -/

/-- The operator on the right-hand side of `pairVecJetAll`: the pairing of the `c`-fold covariant
derivative of `U` on the first `K+c` entries of the tuple with the last entry. -/
noncomputable def Av (g : Submission.Diff.SMet I M) {K : ℕ}
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y) (c : ℕ) :
    (Fin ((K + 1) + c) → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ :=
  fun F y => g.inner y
    (dvc (I := I) (M := M) g K U c (firstPart (I := I) (M := M) F) y)
    (lastPart (I := I) (M := M) F y)

/-! ## Recovering differentiability from the pairings with a smooth ON frame -/

/-- A section whose pairings with the members of a locally orthonormal smooth frame are
differentiable at a point is itself differentiable there. -/
theorem mdiffAtOfPairings (g : Submission.Diff.SMet I M)
    {D : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)}
    {X : Π y : M, TangentSpace I y} {y : M}
    (hON : ∀ᶠ z in 𝓝 y, Submission.Diff.IsONFrame g z (fun i => D i z))
    (hDsm : ∀ i, MDifferentiableAt I I.tangent
      (fun z : M => Bundle.TotalSpace.mk' E z (D i z)) y)
    (h : ∀ i, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun z : M => g.inner z (X z) (D i z)) y) :
    MDifferentiableAt I I.tangent (fun z : M => Bundle.TotalSpace.mk' E z (X z)) y := by
  have hev : (fun z : M => Bundle.TotalSpace.mk' E z (X z))
      =ᶠ[𝓝 y] (fun z : M => Bundle.TotalSpace.mk' E z
        (∑ i, g.inner z (X z) (D i z) • D i z)) := by
    filter_upwards [hON] with z hz
    exact congrArg (fun w : TangentSpace I z => Bundle.TotalSpace.mk' E z w)
      (Work.EXT.sum_inner_smul_eq_self_of_isONFrame (I := I) g z (fun i => D i z) hz (X z)).symm
  refine hev.mdifferentiableAt_iff.mpr ?_
  refine MDifferentiableAt.sum_section (s := Finset.univ) (fun i _ => ?_)
  exact (h i).smul_section (hDsm i)

/-! ## Differentiability of the iterated covariant derivative of `U` -/

/-- **`dvc g K U c T` is differentiable near `x`** for every tuple `T` of smooth fields, provided the
level-`c` pairing identity holds near `x` (and the `JetSmoothOp` hypothesis of the target). -/
theorem dvc_mdiff (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {K : ℕ} (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (hU : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g (K + 1)
      (pairVec (I := I) (M := M) g U) x)
    {W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)}
    (hWsm : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (W i))
    (hWON : ∀ᶠ y in 𝓝 x, Submission.Diff.IsONFrame g y (fun i => W i y))
    {c : ℕ}
    (hid : ∀ H : Fin ((K + 1) + c) → Work.Diff.EXT.TField (I := I) (M := M),
      (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (H i)) →
      jetAll g c (K + 1) (pairVec (I := I) (M := M) g U) H
        =ᶠ[𝓝 x] Av (I := I) (M := M) g U c H)
    (T : Fin (K + c) → Work.Diff.EXT.TField (I := I) (M := M))
    (hT : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (T i)) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt I I.tangent
      (fun z : M => Bundle.TotalSpace.mk' E z (dvc (I := I) (M := M) g K U c T z)) y := by
  have hkey : ∀ i : Fin (Module.finrank ℝ E),
      ∀ᶠ y in 𝓝 x, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
        (fun z : M => g.inner z (dvc (I := I) (M := M) g K U c T z) (W i z)) y := by
    intro i
    have hHsm : ∀ j, Work.Diff.EXT.SmoothF (I := I) (M := M) (extTup K c T (W i) j) :=
      smoothF_extTup hT (hWsm i)
    have hidH : jetAll g c (K + 1) (pairVec (I := I) (M := M) g U) (extTup K c T (W i))
        =ᶠ[𝓝 x] Av (I := I) (M := M) g U c (extTup K c T (W i)) :=
      hid (extTup K c T (W i)) hHsm
    have hjet : ∀ᶠ y in 𝓝 x, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
        (fun z : M => jetAll g c (K + 1) (pairVec (I := I) (M := M) g U)
          (extTup K c T (W i)) z) y :=
      hU.mono (fun y hy => hy c (extTup K c T (W i)) hHsm)
    have hloc : ∀ᶠ y in 𝓝 x,
        (fun z : M => jetAll g c (K + 1) (pairVec (I := I) (M := M) g U)
            (extTup K c T (W i)) z)
          =ᶠ[𝓝 y] (fun z : M => Av (I := I) (M := M) g U c (extTup K c T (W i)) z) :=
      eventually_nhds_of_eventually hidH
    filter_upwards [hloc, hjet] with y hy1 hy2
    have hy3 : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
        (Av (I := I) (M := M) g U c (extTup K c T (W i))) y :=
      hy1.mdifferentiableAt_iff.mp hy2
    have hfun : (Av (I := I) (M := M) g U c (extTup K c T (W i)))
        = fun z : M => g.inner z (dvc (I := I) (M := M) g K U c T z) (W i z) := by
      funext z
      show g.inner z
          (dvc (I := I) (M := M) g K U c
            (firstPart (I := I) (M := M) (extTup K c T (W i))) z)
          (lastPart (I := I) (M := M) (extTup K c T (W i)) z)
        = g.inner z (dvc (I := I) (M := M) g K U c T z) (W i z)
      rw [firstPart_extTup (K := K) (c := c) T (W i),
        lastPart_extTup (K := K) (c := c) T (W i)]
    rw [hfun] at hy3
    exact hy3
  have hWONloc : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, Submission.Diff.IsONFrame g z (fun i => W i z) :=
    eventually_nhds_of_eventually hWON
  filter_upwards [hWONloc, Filter.eventually_all.mpr hkey, Filter.eventually_all.mpr
    (fun i => Filter.Eventually.of_forall
      (fun y => (hWsm i).mdifferentiableAt (by simp)))] with y hyON hykey hyD
  exact mdiffAtOfPairings (I := I) (M := M) g hyON hyD hykey

/-! ## The recursion `extStep g (Av c) =ᶠ Av (c+1)` -/

theorem Av_step (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {K : ℕ} (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (c : ℕ) (F : Fin ((K + 1) + (c + 1)) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i))
    (hdiff : ∀ᶠ y in 𝓝 x, MDifferentiableAt I I.tangent
      (fun z : M => Bundle.TotalSpace.mk' E z
        (dvc (I := I) (M := M) g K U c
          (firstPart (I := I) (M := M) (fun i : Fin ((K + 1) + c) => F i.succ)) z)) y) :
    extStep (I := I) (M := M) g (Av (I := I) (M := M) g U c) F
      =ᶠ[𝓝 x] Av (I := I) (M := M) g U (c + 1) F := by
  have hWsm : Work.Diff.EXT.SmoothF (I := I) (M := M)
      (lastPart (I := I) (M := M) (fun i : Fin ((K + 1) + c) => F i.succ)) := by
    rw [lastPart_eq K c]
    exact hF _
  -- the Leibniz rule for the pairing
  have hleib : ∀ᶠ y in 𝓝 x,
      (mvfderiv I (Av (I := I) (M := M) g U c (fun i : Fin ((K + 1) + c) => F i.succ)) y)
          (F 0 y)
        = g.inner y ((Submission.Diff.lcOf g)
              (dvc (I := I) (M := M) g K U c
                (firstPart (I := I) (M := M) (fun i : Fin ((K + 1) + c) => F i.succ)))
              y (F 0 y))
            (lastPart (I := I) (M := M) (fun i : Fin ((K + 1) + c) => F i.succ) y)
          + g.inner y
              (dvc (I := I) (M := M) g K U c
                (firstPart (I := I) (M := M) (fun i : Fin ((K + 1) + c) => F i.succ)) y)
              ((Submission.Diff.lcOf g)
                (lastPart (I := I) (M := M) (fun i : Fin ((K + 1) + c) => F i.succ)) y (F 0 y)) := by
    filter_upwards [hdiff, Filter.Eventually.of_forall
      (fun y => hWsm.mdifferentiableAt (by simp))] with y hy1 hy2
    exact pairingSplitNB (I := I) (M := M) hLC g hy1 hy2
  -- the corrections
  have hS : ∀ y : M,
      (∑ s : Fin ((K + 1) + c),
        Av (I := I) (M := M) g U c
          (Function.update (fun i : Fin ((K + 1) + c) => F i.succ) s
            (dirF g ((fun i : Fin ((K + 1) + c) => F i.succ) s) (F 0))) y)
        = (∑ r : Fin (K + c), g.inner y
            (dvc (I := I) (M := M) g K U c
              (Function.update (fun i : Fin (K + c) => (firstPart (I := I) (M := M) F) i.succ) r
                (dirF g ((fun i : Fin (K + c) => (firstPart (I := I) (M := M) F) i.succ) r)
                  (F 0))) y)
            (lastPart (I := I) (M := M) F y))
          + g.inner y
              (dvc (I := I) (M := M) g K U c
                (fun i : Fin (K + c) => (firstPart (I := I) (M := M) F) i.succ) y)
              ((Submission.Diff.lcOf g) (lastPart (I := I) (M := M) F) y (F 0 y)) := by
    intro y
    rw [sum_emb (K := K) (c := c)
      (f := fun s => Av (I := I) (M := M) g U c
        (Function.update (fun i : Fin ((K + 1) + c) => F i.succ) s
          (dirF g ((fun i : Fin ((K + 1) + c) => F i.succ) s) (F 0))) y)]
    congr 1
    · refine Finset.sum_congr rfl (fun r _ => ?_)
      simp only [Av]
      have harg := arg_eq_emb K c (fun i : Fin ((K + 1) + c) => F i.succ) r
      rw [firstPart_update_emb, lastPart_update_emb, harg,
        firstPart_comp_succ (K := K) (c := c) F, lastPart_comp_succ (K := K) (c := c) F]
    · simp only [Av]
      have hargL := arg_eq_embL K c (fun i : Fin ((K + 1) + c) => F i.succ)
      rw [firstPart_update_embL, lastPart_update_embL, hargL, dirF,
        firstPart_comp_succ (K := K) (c := c) F, lastPart_comp_succ (K := K) (c := c) F]
  -- the assembly
  filter_upwards [hleib, Filter.Eventually.of_forall hS] with y hy hyS
  show (mvfderiv I (Av (I := I) (M := M) g U c (fun i : Fin ((K + 1) + c) => F i.succ)) y)
        (F 0 y)
      - (∑ s : Fin ((K + 1) + c),
          Av (I := I) (M := M) g U c
            (Function.update (fun i : Fin ((K + 1) + c) => F i.succ) s
              (dirF g ((fun i : Fin ((K + 1) + c) => F i.succ) s) (F 0))) y)
    = Av (I := I) (M := M) g U (c + 1) F y
  rw [hy, hyS]
  simp only [Av, dvc_succ, dvStep, firstPart_zero, firstPart_comp_succ, lastPart_comp_succ,
    map_sub, map_sum, sub_apply, Finset.sum_apply]
  have hcancel : ∀ a b c : ℝ, a + b - (c + b) = a - c := fun a b c => by ring
  rw [hcancel]
  congr 1
  rw [ContinuousLinearMap.sum_apply]

/-! ## The base case -/

theorem Av_base (g : Submission.Diff.SMet I M) (x : M) {K : ℕ}
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (F : Fin ((K + 1) + 0) → Work.Diff.EXT.TField (I := I) (M := M)) :
    jetAll g 0 (K + 1) (pairVec (I := I) (M := M) g U) F
      =ᶠ[𝓝 x] Av (I := I) (M := M) g U 0 F := by
  filter_upwards with y
  simp only [jetAll, Av, pairVec, dvc_zero]
  rw [show (fun i : Fin K => F i.castSucc) = firstPart (I := I) (M := M) F from by
        funext i
        exact congrArg F (Fin.ext rfl),
      show F (Fin.last K) = lastPart (I := I) (M := M) F from congrArg F (Fin.ext rfl)]

/-! ## The induction -/

theorem pairVecJetAll_aux (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {K : ℕ} (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (hU : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g (K + 1)
      (pairVec (I := I) (M := M) g U) x) :
    ∀ c (F : Fin ((K + 1) + c) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
      jetAll g c (K + 1) (pairVec (I := I) (M := M) g U) F
        =ᶠ[𝓝 x] Av (I := I) (M := M) g U c F := by
  obtain ⟨W, hWsm, hWON, -⟩ := Work.Diff.GE.exists_smooth_onframe (I := I) (M := M) g x
  intro c
  induction c with
  | zero =>
      intro F hF
      exact Av_base (I := I) (M := M) g x U F
  | succ c ih =>
      intro F hF
      have hT : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M)
          ((firstPart (I := I) (M := M) (fun i : Fin ((K + 1) + c) => F i.succ)) i) :=
        fun i => hF _
      have hdiff := dvc_mdiff (I := I) (M := M) hLC g x U hU hWsm hWON
        (c := c) ih (firstPart (I := I) (M := M) (fun i : Fin ((K + 1) + c) => F i.succ)) hT
      have hcongr : extStep (I := I) (M := M) g
            (jetAll g c (K + 1) (pairVec (I := I) (M := M) g U)) F
          =ᶠ[𝓝 x] extStep (I := I) (M := M) g (Av (I := I) (M := M) g U c) F :=
        extStep_congr_at (I := I) (M := M) g
          (jetAll g c (K + 1) (pairVec (I := I) (M := M) g U)) (Av (I := I) (M := M) g U c)
          F x
          (ih (fun i => F i.succ) (fun i => hF i.succ))
          (fun s => ih _ (smoothF_update' (fun i => hF i.succ) s
            (dirF_smooth (I := I) (M := M) hLC g (hF _) (hF 0))))
      exact hcongr.trans (Av_step (I := I) (M := M) hLC g x U c F hF hdiff)

end Aux

theorem pairVecJetAll
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) {K : ℕ}
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (hU : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g (K + 1)
      (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g U) x)
    (c : ℕ) (F : Fin ((K + 1) + c) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    Filter.EventuallyEq (nhds x)
      (fun y : M => Work.Diff.EXT.jetAll g c (K + 1)
        (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g U) F y)
      (fun y : M => g.inner y
        (Work.Diff.EXT.evolX.dvc (I := I) (M := M) g K U c
          (Work.Diff.EXT.evolX.firstPart (I := I) (M := M) F) y)
        (Work.Diff.EXT.evolX.lastPart (I := I) (M := M) F y)) :=
  pairVecJetAll_aux (I := I) (M := M) hLC g x U hU c F hF

end Work.Diff.EXT.evolX
