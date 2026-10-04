import Mathlib
import Submission.Work.Diff.EXT.gen.AseqG_eq_PsiG

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Agreement of the time Taylor coefficients at the hyperplane (generic, local form)

`Submission/Work/Diff/EXT/pde_splice.lean` proves, for `ℝ × ℝⁿ → ℝᵐ`, that two solutions of the
same quasilinear system have the same time Taylor coefficients at every point `(T,x)` of the
hyperplane provided their `t = T` slices agree on an open set.  This file carries those lemmas over
to arbitrary real normed spaces `E`, `F`:

* `sJetG_slice_congr`, `sJetG_slice_congr_of_open` (spatial jets agree on the hyperplane),
* `time_derivs_agree_at_hyperplane` (the composite statement used in the assembly),
* `iteratedDeriv_eq_AseqG_at_hyperplane` (the one-sided limit of the iterated time derivative).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
open scoped ContDiff Topology
open Filter

namespace Work.Diff.EXT.gen

open Work.Diff.EXT (sJetG tderivG AseqG SeqG PsiG JG)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Congruence of the spatial `2`-jet on the hyperplane under agreement of the slice functions. -/
theorem sJetG_slice_congr {T : ℝ} {x : E} {g h : ℝ × E → F}
    (hgh : (fun y => g (T, y)) =ᶠ[nhds x] (fun y => h (T, y))) :
    sJetG g (T, x) = sJetG h (T, x) := by
  have h1 : g (T, x) = h (T, x) := hgh.eq_of_nhds
  have h2 : fderiv ℝ (fun y => g (T, y)) x = fderiv ℝ (fun y => h (T, y)) x :=
    (hgh.fderiv (𝕜 := ℝ)).eq_of_nhds
  have h3 : fderiv ℝ (fun w => fderiv ℝ (fun y => g (T, y)) w) x
      = fderiv ℝ (fun w => fderiv ℝ (fun y => h (T, y)) w) x :=
    ((hgh.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).eq_of_nhds
  simp only [sJetG, h1, h2, h3]

/-- On a common open set the slice functions agree, hence so do the spatial `2`-jets. -/
theorem sJetG_slice_congr_of_open {T : ℝ} {U : Set E} (hUo : IsOpen U)
    {x : E} (hx : x ∈ U) {g h : ℝ × E → F} (hgh : ∀ y ∈ U, g (T, y) = h (T, y)) :
    sJetG g (T, x) = sJetG h (T, x) :=
  sJetG_slice_congr (by
    filter_upwards [hUo.mem_nhds hx] with y hy
    exact hgh y hy)

/-- **Agreement of the time Taylor coefficients at the hyperplane.**  If the `t = T` slices of `u`
and `v` agree on an open set `U`, if the recursion identities at the hyperplane hold for both, and
if `∂ₜ^{j+1} = AseqG Φ · j` for both, then all the time Taylor coefficients of `u` and `v` agree at
`(T,x)` for every `x ∈ U`. -/
theorem time_derivs_agree_at_hyperplane (Φ : E × JG E F → F) {T : ℝ}
    {u v : ℝ × E → F} {U : Set E} (hUo : IsOpen U) (hUV : ∀ x ∈ U, u (T, x) = v (T, x))
    (hu_T : ∀ x ∈ U, ∀ j : ℕ,
      AseqG Φ u j (T, x) = PsiG Φ j (x, fun i : Fin (j + 1) => sJetG (SeqG Φ u i) (T, x)))
    (hv_T : ∀ x ∈ U, ∀ j : ℕ,
      AseqG Φ v j (T, x) = PsiG Φ j (x, fun i : Fin (j + 1) => sJetG (SeqG Φ v i) (T, x)))
    (hkey_u : ∀ x ∈ U, ∀ j : ℕ,
      iteratedDeriv (j + 1) (fun s : ℝ => u (s, x)) T = AseqG Φ u j (T, x))
    (hkey_v : ∀ x ∈ U, ∀ j : ℕ,
      iteratedDeriv (j + 1) (fun s : ℝ => v (s, x)) T = AseqG Φ v j (T, x)) :
    ∀ x ∈ U, ∀ i : ℕ,
      iteratedDeriv i (fun s : ℝ => u (s, x)) T = iteratedDeriv i (fun s : ℝ => v (s, x)) T := by
  have hjet : ∀ x ∈ U, sJetG u (T, x) = sJetG v (T, x) :=
    fun x hx => sJetG_slice_congr_of_open hUo hx hUV
  have hAC : ∀ j : ℕ, ∀ x ∈ U, AseqG Φ u j (T, x) = AseqG Φ v j (T, x) := by
    intro j
    refine Nat.strong_induction_on (p := fun j => ∀ x ∈ U,
      AseqG Φ u j (T, x) = AseqG Φ v j (T, x)) j ?_
    intro j ih x hx
    match j with
    | 0 =>
      simp only [AseqG]
      rw [hjet x hx]
    | (j' + 1) =>
      rw [hu_T x hx (j' + 1), hv_T x hx (j' + 1)]
      have hjeq : (fun i : Fin (j' + 2) => sJetG (SeqG Φ u i) (T, x))
          = (fun i : Fin (j' + 2) => sJetG (SeqG Φ v i) (T, x)) := by
        funext i
        induction i using Fin.cases with
        | zero => exact hjet x hx
        | succ k =>
          refine sJetG_slice_congr_of_open hUo hx (fun y hy => ?_)
          exact ih k.val k.isLt y hy
      rw [hjeq]
  intro x hx i
  rcases i with _ | j
  · simpa using hUV x hx
  · rw [hkey_u x hx j, hkey_v x hx j, hAC j x hx]

/-- The iterated derivatives of a function that is `C^∞` at a point are `C^∞` at that point. -/
theorem contDiffAt_iteratedDeriv {f : ℝ → F} {T : ℝ} (hf : ContDiffAt ℝ (⊤ : ℕ∞) f T) :
    ∀ n : ℕ, ContDiffAt ℝ (⊤ : ℕ∞) (iteratedDeriv n f) T := by
  intro n
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hfd : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ (iteratedDeriv n f)) T :=
      ih.fderiv_right (by simp)
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun t : ℝ => fderiv ℝ (iteratedDeriv n f) t 1) T :=
      hfd.clm_apply contDiffAt_const
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    exact (fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := iteratedDeriv n f) (x := t)).symm

/-- The `(j+1)`-st time derivative at the hyperplane, computed as the limit along a curve inside
the half-space where the equation holds. -/
theorem iteratedDeriv_eq_AseqG_at_hyperplane (Φ : E × JG E F → F)
    {w : ℝ × E → F} {S : Set (ℝ × E)} {T : ℝ} {x : E} {j : ℕ}
    (hw : ContDiffAt ℝ (⊤ : ℕ∞) w (T, x))
    (hrec : ∀ z ∈ S, AseqG Φ w j z = iteratedDeriv (j + 1) (fun s => w (s, z.2)) z.1)
    (hA_cont : ContinuousAt (AseqG Φ w j) (T, x))
    (c : ℝ → ℝ) (hc : Tendsto c (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds T))
    (hcmem : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)), (c ε, x) ∈ S) :
    iteratedDeriv (j + 1) (fun s : ℝ => w (s, x)) T = AseqG Φ w j (T, x) := by
  have hwx : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => w (s, x)) T := by
    have h := ContDiffAt.comp T hw (contDiffAt_id.prodMk contDiffAt_const)
    simpa [Function.comp_def] using h
  have hcont1 : ContinuousAt (fun t : ℝ => iteratedDeriv (j + 1) (fun s : ℝ => w (s, x)) t) T :=
    (contDiffAt_iteratedDeriv hwx (j + 1)).continuousAt
  have ht1 : Tendsto (fun ε : ℝ => iteratedDeriv (j + 1) (fun s : ℝ => w (s, x)) (c ε))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (iteratedDeriv (j + 1) (fun s : ℝ => w (s, x)) T)) :=
    hcont1.tendsto.comp hc
  have ht2 : Tendsto (fun ε : ℝ => iteratedDeriv (j + 1) (fun s : ℝ => w (s, x)) (c ε))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (AseqG Φ w j (T, x))) := by
    have h3 : Tendsto (fun ε : ℝ => AseqG Φ w j (c ε, x)) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (AseqG Φ w j (T, x))) :=
      hA_cont.tendsto.comp (hc.prodMk_nhds tendsto_const_nhds)
    refine h3.congr' ?_
    filter_upwards [hcmem] with ε hε
    exact hrec (c ε, x) hε
  exact tendsto_nhds_unique ht1 ht2


/-- From a local equality of the slice functions we get an open set on which they agree. -/
theorem exists_open_slice_eq {T : ℝ} {x₀ : E} {u v : ℝ × E → F}
    (h : (fun y => u (T, y)) =ᶠ[nhds x₀] (fun y => v (T, y))) :
    ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧ ∀ x ∈ U, u (T, x) = v (T, x) := by
  have hmem : {x : E | u (T, x) = v (T, x)} ∈ nhds x₀ := h
  obtain ⟨U, hUsub, hUo, hxU⟩ := mem_nhds_iff.mp hmem
  exact ⟨U, hUo, hxU, fun x hx => hUsub hx⟩

/-- The recursion extends to the hyperplane along a curve approaching it inside `S`. -/
theorem AseqG_eq_PsiG_at_of_curve (Φ : E × JG E F → F)
    {a : ℝ × E → F} {S : Set (ℝ × E)} {T : ℝ} {x : E}
    (hrec : ∀ j : ℕ, ∀ z ∈ S,
      AseqG Φ a j z = PsiG Φ j (z.2, fun i : Fin (j + 1) => sJetG (SeqG Φ a i) z))
    (hA_cont : ∀ j : ℕ, ContinuousAt (AseqG Φ a j) (T, x))
    (hPsi_cont : ∀ j : ℕ, ContinuousAt
      (fun z : ℝ × E => PsiG Φ j (z.2, fun i : Fin (j + 1) => sJetG (SeqG Φ a i) z)) (T, x))
    (c : ℝ → ℝ) (hc : Tendsto c (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds T))
    (hcmem : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)), (c ε, x) ∈ S) (j : ℕ) :
    AseqG Φ a j (T, x) = PsiG Φ j (x, fun i : Fin (j + 1) => sJetG (SeqG Φ a i) (T, x)) := by
  have hcur : Tendsto (fun ε : ℝ => (c ε, x)) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (T, x)) :=
    hc.prodMk_nhds tendsto_const_nhds
  have h1 : Tendsto (fun ε : ℝ => AseqG Φ a j (c ε, x)) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (AseqG Φ a j (T, x))) := (hA_cont j).tendsto.comp hcur
  have h2 : Tendsto (fun ε : ℝ => AseqG Φ a j (c ε, x)) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (PsiG Φ j (x, fun i : Fin (j + 1) => sJetG (SeqG Φ a i) (T, x)))) := by
    refine ((hPsi_cont j).tendsto.comp hcur).congr' ?_
    filter_upwards [hcmem] with ε hε
    exact (hrec j (c ε, x) hε).symm
  exact tendsto_nhds_unique h1 h2

end Work.Diff.EXT.gen
