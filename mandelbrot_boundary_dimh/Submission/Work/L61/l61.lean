import Mathlib
import Submission.Work.L61.Basic
import Submission.Work.L61.Chain.isCompact_Kset
import Submission.Work.L61.Preimage.preimage_infinite
import Submission.Work.L61.Preimage.periodic_preimage_unique
import Submission.Work.L61.Deriv.E_deriv_ne_zero
import Submission.Work.L61.Deriv.deriv_ne_zero
import Submission.Work.L61.Covering.covering
import Submission.Work.L61.Branch.exists_branch
import Submission.Work.L61.Branch.branch_eqOn
import Submission.Work.L61.Chain.ball_chain
import Submission.Work.L61.Repel.exists_repelling_orbit
import Submission.Work.L61.Normal.tendsto_zero_of_normal
import Submission.Work.L61.Normal.tendsto_zero_propagate
import Submission.Work.Normal.montel_omits_three

/-!
# Lemma 6.1 (Shishikura §6): the proof

`L61Statement` is proved by the paper's argument.  The pieces are:

* `Submission/Work/L61/Basic` — the pushed-down horn map `g = pushdown Ẽ_{f₀}`, its domain
  `gdom`, its critical value `critVal` and the critical orbit `Kset`.
* `Work.L61.Covering.covering` — `g` is a covering map on `gdom` minus the critical points,
  over the complement of `Kset`.
* `Work.L61.Branch.exists_branch` / `branch_eqOn` — inverse branches of `g` through that
  covering, with prescribed values, and their uniqueness.
* `Work.L61.Chain.ball_chain` — a chain of balls avoiding `Kset`, joining `w₁`, `w₁'` and the
  repelling-orbit point `wd 0`.
* `Work.L61.Repel.exists_repelling_orbit` — an inverse orbit `wd → 0` of `g`.
* `Work.L61.Normal.*` — normality (`montel_two_omitted`) and Hurwitz give `G_j → 0`.

The family `G j i` of inverse branches of `g^j` on the `i`-th ball of the chain is built by
recursion on `j`, walking down the chain from the anchor ball so that the branch at the anchor
is pinned by `wd j` and each earlier branch is pinned by its successor at a shared point.
-/

namespace Work.L61

open MandelDim Set Function Metric Filter
open Work.Normal
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

/-- The chain datum: `N+1` balls avoiding the critical orbit, consecutive ones intersecting. -/
structure ChainData {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (hd : HornData d) where
  N : ℕ
  cen : Fin (N + 1) → ℂ
  rad : Fin (N + 1) → ℝ
  ib : Fin (N + 1)
  rad_pos : ∀ i, 0 < rad i
  disj : ∀ i, Disjoint (ball (cen i) (rad i)) (Kset d hd)
  pt : Fin N → ℂ
  pt_mem : ∀ i, pt i ∈ ball (cen i.castSucc) (rad i.castSucc)
    ∩ ball (cen i.succ) (rad i.succ)

variable {d : ParabData f₀ D₀} {hd : HornData d}

/-- The `i`-th ball of the chain. -/
def U (S : ChainData d hd) (i : Fin (S.N + 1)) : Set ℂ := ball (S.cen i) (S.rad i)

theorem U_open (S : ChainData d hd) (i : Fin (S.N + 1)) : IsOpen (U S i) := Metric.isOpen_ball

theorem U_simplyConnected (S : ChainData d hd) (i : Fin (S.N + 1)) : IsSimplyConnected (U S i) := by
  haveI : ContractibleSpace (U S i) :=
    Convex.contractibleSpace (convex_ball _ _) ⟨S.cen i, mem_ball_self (S.rad_pos i)⟩
  exact SimplyConnectedSpace.ofContractible _

theorem U_preconn (S : ChainData d hd) (i : Fin (S.N + 1)) : IsPreconnected (U S i) :=
  (convex_ball _ _).isPreconnected

theorem U_inter_nonempty (S : ChainData d hd) (i : Fin S.N) :
    (U S i.castSucc ∩ U S i.succ).Nonempty :=
  ⟨S.pt i, S.pt_mem i⟩

theorem U_subset_compl (S : ChainData d hd) (i : Fin (S.N + 1)) :
    U S i ⊆ (Kset d hd)ᶜ := fun z hz hzK => (S.disj i).le_bot ⟨hz, hzK⟩

/-- One inverse branch of `g` on `U` over `f`, with prescribed value. -/
noncomputable def liftFn (hcov : IsCoveringMapOn
      (fun ζ : {ζ : ℂ // ζ ∈ gdom d hd ∧ g d ζ ≠ critVal hd} => g d ζ) (Kset d hd)ᶜ)
    {U : Set ℂ} (hUo : IsOpen U) (hUsc : IsSimplyConnected U)
    {f : ℂ → ℂ} (hfhol : DifferentiableOn ℂ f U) (hfK : ∀ z ∈ U, f z ∉ Kset d hd)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {e₀ : ℂ} (he₀ : g d e₀ = f z₀) (he₀d : e₀ ∈ gdom d hd) : ℂ → ℂ :=
  Classical.choose (Branch.exists_branch hd hcov hUo hUsc hfhol hfK hz₀ he₀ he₀d)

theorem liftFn_val (hcov : IsCoveringMapOn
      (fun ζ : {ζ : ℂ // ζ ∈ gdom d hd ∧ g d ζ ≠ critVal hd} => g d ζ) (Kset d hd)ᶜ)
    {U : Set ℂ} (hUo : IsOpen U) (hUsc : IsSimplyConnected U)
    {f : ℂ → ℂ} (hfhol : DifferentiableOn ℂ f U) (hfK : ∀ z ∈ U, f z ∉ Kset d hd)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {e₀ : ℂ} (he₀ : g d e₀ = f z₀) (he₀d : e₀ ∈ gdom d hd) :
    liftFn (d := d) (hd := hd) hcov hUo hUsc hfhol hfK hz₀ he₀ he₀d z₀ = e₀ :=
  (Classical.choose_spec (Branch.exists_branch hd hcov hUo hUsc hfhol hfK hz₀ he₀ he₀d)).1

/-- A branch of `g⁻¹` on `U` over `f`, with the properties the construction keeps. -/
structure BrOk (U : Set ℂ) (f : ℂ → ℂ) (ψ : ℂ → ℂ) : Prop where
  holo : DifferentiableOn ℂ ψ U
  sec : ∀ z ∈ U, g d (ψ z) = f z
  dom : ∀ z ∈ U, ψ z ∈ gdom d hd
  Kfree : ∀ z ∈ U, ψ z ∉ Kset d hd
  noncrit : ∀ z ∈ U, deriv (g d) (ψ z) ≠ 0

theorem liftFn_brOk (hcov : IsCoveringMapOn
      (fun ζ : {ζ : ℂ // ζ ∈ gdom d hd ∧ g d ζ ≠ critVal hd} => g d ζ) (Kset d hd)ᶜ)
    {U : Set ℂ} (hUo : IsOpen U) (hUsc : IsSimplyConnected U)
    {f : ℂ → ℂ} (hfhol : DifferentiableOn ℂ f U) (hfK : ∀ z ∈ U, f z ∉ Kset d hd)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {e₀ : ℂ} (he₀ : g d e₀ = f z₀) (he₀d : e₀ ∈ gdom d hd) :
    BrOk (d := d) (hd := hd) U f
      (liftFn (d := d) (hd := hd) hcov hUo hUsc hfhol hfK hz₀ he₀ he₀d) := by
  have h := Classical.choose_spec (Branch.exists_branch (d := d) (hd := hd) hcov hUo hUsc hfhol hfK hz₀ he₀ he₀d)
  exact ⟨h.2.2.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- The invariant of the level-`j` family of inverse branches. -/
structure FamOk (S : ChainData d hd) (wd : ℕ → ℂ) (j : ℕ) (G : Fin (S.N + 1) → ℂ → ℂ) : Prop where
  holo : ∀ i, DifferentiableOn ℂ (G i) (U S i)
  abel : ∀ i z, z ∈ U S i → (g d)^[j] (G i z) = z
  dom : ∀ i z, z ∈ U S i → 1 ≤ j → G i z ∈ gdom d hd
  Kfree : ∀ i z, z ∈ U S i → G i z ∉ Kset d hd
  noncrit : ∀ i z, z ∈ U S i → 1 ≤ j → deriv (g d) (G i z) ≠ 0
  compat : ∀ i : Fin S.N, Set.EqOn (G i.castSucc) (G i.succ) (U S i.castSucc ∩ U S i.succ)
  anchor : G (Fin.last S.N) (wd 0) = wd j

section Step

variable {S : ChainData d hd} {wd : ℕ → ℂ} {j : ℕ} {prev : Fin (S.N + 1) → ℂ → ℂ}

/-- The bridge value at the shared point `pt k`: the value prescribed for the branch at
`k.castSucc` is the value of the already-constructed branch at `k.succ`. -/
theorem bridge_eq (hprev : FamOk S wd j prev) {k : Fin S.N}
    (nextv : {ψ : ℂ → ℂ // BrOk (d := d) (hd := hd) (U S k.succ) (prev k.succ) ψ}) :
    g d (nextv.1 (S.pt k)) = prev k.castSucc (S.pt k) := by
  rw [nextv.2.sec (S.pt k) (S.pt_mem k).2]
  exact (hprev.compat k (S.pt_mem k)).symm

variable (hcov : IsCoveringMapOn
    (fun ζ : {ζ : ℂ // ζ ∈ gdom d hd ∧ g d ζ ≠ critVal hd} => g d ζ) (Kset d hd)ᶜ)

/-- The branch at the anchor end of the chain. -/
noncomputable def stepBase (hprev : FamOk S wd j prev) (hwd0 : wd 0 ∈ U S (Fin.last S.N))
    (hwdg : ∀ j, g d (wd (j + 1)) = wd j) (hwddom : ∀ j, wd (j + 1) ∈ gdom d hd) :
    {ψ : ℂ → ℂ // BrOk (d := d) (hd := hd) (U S (Fin.last S.N)) (prev (Fin.last S.N)) ψ} :=
  ⟨liftFn (d := d) (hd := hd) hcov (U_open S (Fin.last S.N)) (U_simplyConnected S (Fin.last S.N))
      (hprev.holo _) (hprev.Kfree _) hwd0 (by rw [hwdg j, hprev.anchor]) (hwddom j),
    liftFn_brOk (d := d) (hd := hd) hcov (U_open S (Fin.last S.N)) (U_simplyConnected S (Fin.last S.N))
      (hprev.holo _) (hprev.Kfree _) hwd0 (by rw [hwdg j, hprev.anchor]) (hwddom j)⟩

theorem stepBase_val (hprev : FamOk S wd j prev) (hwd0 : wd 0 ∈ U S (Fin.last S.N))
    (hwdg : ∀ j, g d (wd (j + 1)) = wd j) (hwddom : ∀ j, wd (j + 1) ∈ gdom d hd) :
    (stepBase hcov hprev hwd0 hwdg hwddom).1 (wd 0) = wd (j + 1) :=
  liftFn_val (d := d) (hd := hd) hcov (U_open S (Fin.last S.N)) (U_simplyConnected S (Fin.last S.N))
    (hprev.holo _) (hprev.Kfree _) hwd0 (by rw [hwdg j, hprev.anchor]) (hwddom j)

/-- One step down the chain: the branch at `k.castSucc` is pinned by the value of the branch at
`k.succ` at the shared point. -/
noncomputable def stepStep (hprev : FamOk S wd j prev) (hwd0 : wd 0 ∈ U S (Fin.last S.N))
    (hwdg : ∀ j, g d (wd (j + 1)) = wd j) (hwddom : ∀ j, wd (j + 1) ∈ gdom d hd) (k : Fin S.N)
    (nextv : {ψ : ℂ → ℂ // BrOk (d := d) (hd := hd) (U S k.succ) (prev k.succ) ψ}) :
    {ψ : ℂ → ℂ // BrOk (d := d) (hd := hd) (U S k.castSucc) (prev k.castSucc) ψ} :=
  ⟨liftFn (d := d) (hd := hd) hcov (U_open S k.castSucc) (U_simplyConnected S k.castSucc)
      (hprev.holo _) (hprev.Kfree _) (S.pt_mem k).1 (bridge_eq hprev nextv) (nextv.2.dom _ (S.pt_mem k).2),
    liftFn_brOk (d := d) (hd := hd) hcov (U_open S k.castSucc) (U_simplyConnected S k.castSucc)
      (hprev.holo _) (hprev.Kfree _) (S.pt_mem k).1 (bridge_eq hprev nextv) (nextv.2.dom _ (S.pt_mem k).2)⟩

theorem stepStep_val (hprev : FamOk S wd j prev) (hwd0 : wd 0 ∈ U S (Fin.last S.N))
    (hwdg : ∀ j, g d (wd (j + 1)) = wd j) (hwddom : ∀ j, wd (j + 1) ∈ gdom d hd) (k : Fin S.N)
    (nextv : {ψ : ℂ → ℂ // BrOk (d := d) (hd := hd) (U S k.succ) (prev k.succ) ψ}) :
    (stepStep hcov hprev hwd0 hwdg hwddom k nextv).1 (S.pt k) = nextv.1 (S.pt k) :=
  liftFn_val (d := d) (hd := hd) hcov (U_open S k.castSucc) (U_simplyConnected S k.castSucc)
    (hprev.holo _) (hprev.Kfree _) (S.pt_mem k).1 (bridge_eq hprev nextv) (nextv.2.dom _ (S.pt_mem k).2)

/-- The level `j+1` family: lift the level `j` family through `g`, walking down the chain. -/
noncomputable def stepFun (hprev : FamOk S wd j prev) (hwd0 : wd 0 ∈ U S (Fin.last S.N))
    (hwdg : ∀ j, g d (wd (j + 1)) = wd j) (hwddom : ∀ j, wd (j + 1) ∈ gdom d hd) :
    Fin (S.N + 1) → ℂ → ℂ :=
  fun i => (Fin.reverseInduction (motive := fun i => {ψ : ℂ → ℂ // BrOk (d := d) (hd := hd) (U S i) (prev i) ψ})
    (stepBase hcov hprev hwd0 hwdg hwddom)
    (fun k nextv => stepStep hcov hprev hwd0 hwdg hwddom k nextv) i).1

theorem stepFun_brOk (hprev : FamOk S wd j prev) (hwd0 : wd 0 ∈ U S (Fin.last S.N))
    (hwdg : ∀ j, g d (wd (j + 1)) = wd j) (hwddom : ∀ j, wd (j + 1) ∈ gdom d hd) (i : Fin (S.N + 1)) :
    BrOk (d := d) (hd := hd) (U S i) (prev i) (stepFun hcov hprev hwd0 hwdg hwddom i) :=
  (Fin.reverseInduction (motive := fun i => {ψ : ℂ → ℂ // BrOk (d := d) (hd := hd) (U S i) (prev i) ψ})
    (stepBase hcov hprev hwd0 hwdg hwddom)
    (fun k nextv => stepStep hcov hprev hwd0 hwdg hwddom k nextv) i).2

theorem stepFun_castSucc (hprev : FamOk S wd j prev) (hwd0 : wd 0 ∈ U S (Fin.last S.N))
    (hwdg : ∀ j, g d (wd (j + 1)) = wd j) (hwddom : ∀ j, wd (j + 1) ∈ gdom d hd) (k : Fin S.N) :
    stepFun hcov hprev hwd0 hwdg hwddom k.castSucc
      = (stepStep hcov hprev hwd0 hwdg hwddom k
          (Fin.reverseInduction (motive := fun i => {ψ : ℂ → ℂ // BrOk (d := d) (hd := hd) (U S i) (prev i) ψ})
            (stepBase hcov hprev hwd0 hwdg hwddom)
            (fun k nextv => stepStep hcov hprev hwd0 hwdg hwddom k nextv) k.succ)).1 := by
  rw [stepFun, Fin.reverseInduction_castSucc]

theorem stepFun_last (hprev : FamOk S wd j prev) (hwd0 : wd 0 ∈ U S (Fin.last S.N))
    (hwdg : ∀ j, g d (wd (j + 1)) = wd j) (hwddom : ∀ j, wd (j + 1) ∈ gdom d hd) :
    stepFun hcov hprev hwd0 hwdg hwddom (Fin.last S.N)
      = (stepBase hcov hprev hwd0 hwdg hwddom).1 := by
  rw [stepFun, Fin.reverseInduction_last]

theorem stepFun_compat_val (hprev : FamOk S wd j prev) (hwd0 : wd 0 ∈ U S (Fin.last S.N))
    (hwdg : ∀ j, g d (wd (j + 1)) = wd j) (hwddom : ∀ j, wd (j + 1) ∈ gdom d hd) (k : Fin S.N) :
    stepFun hcov hprev hwd0 hwdg hwddom k.castSucc (S.pt k)
      = stepFun hcov hprev hwd0 hwdg hwddom k.succ (S.pt k) := by
  rw [stepFun_castSucc]
  exact stepStep_val hcov hprev hwd0 hwdg hwddom k _


/-- Shifting a natural number down by one tends to infinity. -/
theorem tendsto_sub_one_atTop : Tendsto (fun k : ℕ => k - 1) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (b + 1)] with k hk
  omega

theorem stepFun_ok (hprev : FamOk S wd j prev) (hwd0 : wd 0 ∈ U S (Fin.last S.N))
    (hwdg : ∀ j, g d (wd (j + 1)) = wd j) (hwddom : ∀ j, wd (j + 1) ∈ gdom d hd) :
    FamOk S wd (j + 1) (stepFun hcov hprev hwd0 hwdg hwddom) where
  holo i := (stepFun_brOk hcov hprev hwd0 hwdg hwddom i).holo
  abel i z hz := by
    rw [Function.iterate_succ_apply, (stepFun_brOk hcov hprev hwd0 hwdg hwddom i).sec z hz]
    exact hprev.abel i z hz
  dom i z hz _ := (stepFun_brOk hcov hprev hwd0 hwdg hwddom i).dom z hz
  Kfree i z hz := (stepFun_brOk hcov hprev hwd0 hwdg hwddom i).Kfree z hz
  noncrit i z hz _ := (stepFun_brOk hcov hprev hwd0 hwdg hwddom i).noncrit z hz
  compat i z hz := by
    refine Branch.branch_eqOn (d := d) (hd := hd) hcov (Metric.isOpen_ball.inter Metric.isOpen_ball)
      ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected (f := prev i.castSucc)
      (z₀ := S.pt i) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz
    · intro u hu
      exact hprev.Kfree i.castSucc u hu.1
    · intro u hu
      exact (stepFun_brOk hcov hprev hwd0 hwdg hwddom i.castSucc).sec u hu.1
    · intro u hu
      rw [(stepFun_brOk hcov hprev hwd0 hwdg hwddom i.succ).sec u hu.2]
      exact (hprev.compat i hu).symm
    · exact ((stepFun_brOk hcov hprev hwd0 hwdg hwddom i.castSucc).holo.continuousOn).mono
        Set.inter_subset_left
    · exact ((stepFun_brOk hcov hprev hwd0 hwdg hwddom i.succ).holo.continuousOn).mono
        Set.inter_subset_right
    · intro u hu
      exact ⟨(stepFun_brOk hcov hprev hwd0 hwdg hwddom i.castSucc).dom u hu.1,
        (stepFun_brOk hcov hprev hwd0 hwdg hwddom i.succ).dom u hu.2⟩
    · exact S.pt_mem i
    · exact stepFun_compat_val hcov hprev hwd0 hwdg hwddom i
  anchor := by
    rw [stepFun_last]
    exact stepBase_val hcov hprev hwd0 hwdg hwddom

end Step

section Family

variable {S : ChainData d hd} {wd : ℕ → ℂ}

/-- The level-`j` family of inverse branches, with its invariants (recursion on `j`). -/
noncomputable def famAux (hcov : IsCoveringMapOn
      (fun ζ : {ζ : ℂ // ζ ∈ gdom d hd ∧ g d ζ ≠ critVal hd} => g d ζ) (Kset d hd)ᶜ)
    (S : ChainData d hd) (wd : ℕ → ℂ) (hwd0 : wd 0 ∈ U S (Fin.last S.N))
    (hwdg : ∀ j, g d (wd (j + 1)) = wd j) (hwddom : ∀ j, wd (j + 1) ∈ gdom d hd) :
    (j : ℕ) → {G : Fin (S.N + 1) → ℂ → ℂ // FamOk S wd j G}
  | 0 => ⟨fun _ => id, {
      holo := fun i => differentiableOn_id
      abel := by intro i z hz; simp
      dom := by intro i z hz hj; exact absurd hj (by omega)
      Kfree := by intro i z hz; exact U_subset_compl S i hz
      noncrit := by intro i z hz hj; exact absurd hj (by omega)
      compat := by intro i z hz; rfl
      anchor := by simp }⟩
  | (j + 1) => ⟨stepFun hcov (famAux hcov S wd hwd0 hwdg hwddom j).2 hwd0 hwdg hwddom,
      stepFun_ok hcov (famAux hcov S wd hwd0 hwdg hwddom j).2 hwd0 hwdg hwddom⟩

/-- Iterating `g` on `0` gives `0`. -/
theorem iterate_g_zero (k : ℕ) : (g d)^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, g_zero]

end Family

theorem l61 : L61Statement := by
  intro f₀ D₀ hF0 d hd w₀ hw₀ne hw₀gdom
  have hcv : w₀ ≠ critVal hd := fun h => hw₀gdom (h ▸ critVal_mem_gdom d hd)
  have hcv0 : (0 : ℂ) ≠ critVal hd := (critVal_ne_zero hd).symm
  have hw₀K : w₀ ∉ Kset d hd := fun h => hw₀gdom (Kset_subset_gdom d hd h)
  have hKc : (Kset d hd).Countable := (Set.countable_singleton 0).union (Set.countable_range _)
  have hKcomp : IsCompact (Kset d hd) := isCompact_Kset hd
  have hcov := Covering.covering (d := d) hd
  ------------------------------------------------------------------
  -- two distinct non-periodic preimages of `w₀`
  ------------------------------------------------------------------
  set Sset : Set ℂ := {ζ : ℂ | ζ ∈ gdom d hd ∧ g d ζ = w₀} with hSset
  set Per : Set ℂ := {z : ℂ | ∃ n : ℕ, 1 ≤ n ∧ (g d)^[n] z = z} with hPer
  have hSinf : Sset.Infinite := by rw [hSset]; exact preimage_infinite hd hw₀gdom
  have hPerfin : (Sset ∩ Per).Finite := by
    refine Set.Subsingleton.finite ?_
    rintro p ⟨hp, hpp⟩ q ⟨hq, hqq⟩
    exact periodic_preimage_unique hp.2 hq.2 hpp hqq
  obtain ⟨w₁, hw₁⟩ := (hSinf.diff hPerfin).nonempty
  obtain ⟨w₁', hw₁'⟩ := ((hSinf.diff hPerfin).diff (Set.finite_singleton w₁)).nonempty
  have hw₁S : w₁ ∈ Sset := hw₁.1
  have hw₁per : w₁ ∉ Per := fun hp => hw₁.2 ⟨hw₁.1, hp⟩
  have hw₁'S : w₁' ∈ Sset := hw₁'.1.1
  have hw₁'per : w₁' ∉ Per := fun hp => hw₁'.1.2 ⟨hw₁'.1.1, hp⟩
  have hne' : w₁ ≠ w₁' := by
    intro h
    exact hw₁'.2 (Set.mem_singleton_iff.mpr h.symm)
  have hw₁mem : w₁ ∈ gdom d hd := hw₁S.1
  have hgw₁ : g d w₁ = w₀ := hw₁S.2
  have hw₁'mem : w₁' ∈ gdom d hd := hw₁'S.1
  have hgw₁' : g d w₁' = w₀ := hw₁'S.2
  have hw₁K : w₁ ∉ Kset d hd := fun h => hw₀K (hgw₁ ▸ mapsTo_Kset d hd h)
  have hw₁'K : w₁' ∉ Kset d hd := fun h => hw₀K (hgw₁' ▸ mapsTo_Kset d hd h)
  have hw₁ne0 : w₁ ≠ 0 := by
    intro h
    rw [h, g_zero] at hgw₁
    exact hw₀ne hgw₁.symm
  ------------------------------------------------------------------
  -- a repelling inverse orbit `wd → 0`
  ------------------------------------------------------------------
  obtain ⟨wd, hwdne, hwdK, hwddom, hwdg, hwdTend⟩ := Repel.exists_repelling_orbit (d := d) hd
  ------------------------------------------------------------------
  -- the chain of balls
  ------------------------------------------------------------------
  obtain ⟨N, cen, rad, ib, hrad, hdisj, hw₁U, hw₁'U, hwdU, hchain⟩ :=
    Chain.ball_chain hKc hKcomp hw₁K hw₁'K (hwdK 0)
  let pt : Fin N → ℂ := fun i => Classical.choose (hchain i)
  have hpt : ∀ i, pt i ∈ ball (cen i.castSucc) (rad i.castSucc) ∩ ball (cen i.succ) (rad i.succ) :=
    fun i => Classical.choose_spec (hchain i)
  let S : ChainData d hd := ⟨N, cen, rad, ib, hrad, hdisj, pt, hpt⟩
  have hwdU' : wd 0 ∈ U S (Fin.last S.N) := hwdU
  have hwnU : w₁ ∈ U S 0 := hw₁U
  have hwmU : w₁' ∈ U S ib := hw₁'U
  let hfam := famAux hcov S wd hwdU' hwdg hwddom
  let G : ℕ → (Fin (S.N + 1) → ℂ → ℂ) := fun j => (hfam j).1
  have hfamOk : ∀ j, FamOk S wd j (G j) := fun j => (hfam j).2
  have hGsucc : ∀ j, G (j + 1) = stepFun hcov (hfamOk j) hwdU' hwdg hwddom := by
    intro j
    simp only [G, hfam, famAux]
  have hGsec : ∀ j i z, z ∈ U S i → g d (G (j + 1) i z) = G j i z := by
    intro j i z hz
    rw [hGsucc j]
    exact (stepFun_brOk hcov (hfamOk j) hwdU' hwdg hwddom i).sec z hz
  ------------------------------------------------------------------
  -- the two sequences
  ------------------------------------------------------------------
  let wa : ℕ → ℂ := fun k => if k = 0 then w₀ else G (k - 1) 0 w₁
  let wb : ℕ → ℂ := fun k => if k = 0 then w₀ else G (k - 1) ib w₁'
  have hwa1 : ∀ j, wa (j + 1) = G j 0 w₁ := by
    intro j
    simp only [wa]
    rw [if_neg (by omega : ¬ (j + 1 = 0)), show j + 1 - 1 = j by omega]
  have hwb1 : ∀ j, wb (j + 1) = G j ib w₁' := by
    intro j
    simp only [wb]
    rw [if_neg (by omega : ¬ (j + 1 = 0)), show j + 1 - 1 = j by omega]
  have hwa0 : wa 0 = w₀ := by simp [wa]
  have hwb0 : wb 0 = w₀ := by simp [wb]
  have hG0id : G 0 = fun _ => (id : ℂ → ℂ) := by simp only [G, hfam, famAux]
  have hwa_orbit : ∀ j, g d (wa (j + 1)) = wa j := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hwa1 0, hwa0]
      change g d (G 0 (0 : Fin (S.N + 1)) w₁) = w₀
      rw [show G 0 (0 : Fin (S.N + 1)) w₁ = w₁ from by rw [hG0id]; rfl, hgw₁]
    · rw [hwa1 j, show wa j = G (j - 1) 0 w₁ from by
          simp only [wa, if_neg (by omega : ¬ (j = 0))]]
      rw [← show j - 1 + 1 = j by omega]
      exact hGsec (j - 1) 0 w₁ hwnU
  have hwb_orbit : ∀ j, g d (wb (j + 1)) = wb j := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hwb1 0, hwb0]
      change g d (G 0 (ib : Fin (S.N + 1)) w₁') = w₀
      rw [show G 0 ib w₁' = w₁' from by rw [hG0id]; rfl, hgw₁']
    · rw [hwb1 j, show wb j = G (j - 1) ib w₁' from by
          simp only [wb, if_neg (by omega : ¬ (j = 0))]]
      rw [← show j - 1 + 1 = j by omega]
      exact hGsec (j - 1) ib w₁' hwmU
  ------------------------------------------------------------------
  -- non-vanishing of the branches; normality
  ------------------------------------------------------------------
  have hG_ne0 : ∀ j i z, z ∈ U S i → G j i z ≠ 0 := by
    intro j i z hz h
    have hz' := (hfamOk j).abel i z hz
    rw [h, iterate_g_zero] at hz'
    exact Set.disjoint_left.mp (S.disj i) hz (hz' ▸ zero_mem_Kset d hd)
  have hG_nec : ∀ j i z, z ∈ U S i → G j i z ≠ critVal hd := by
    intro j i z hz h
    have hz' := (hfamOk j).abel i z hz
    rw [h] at hz'
    exact Set.disjoint_left.mp (S.disj i) hz (hz' ▸ Kset_crit_orbit d hd j)
  have hnorm : ∀ i, Work.Normal.IsNormalFamily (Set.range (fun j => G j i)) (U S i) := by
    intro i
    refine montel_two_omitted hcv0 (U_open S i) (U_preconn S i) ?_ ?_
    · rintro v ⟨j, rfl⟩
      exact (hfamOk j).holo i
    · rintro v ⟨j, rfl⟩ z hz
      exact ⟨hG_ne0 j i z hz, hG_nec j i z hz⟩
  ------------------------------------------------------------------
  -- convergence to `0`, propagated down the chain
  ------------------------------------------------------------------
  have hconvTop : TendstoLocallyUniformlyOn (fun j => G j (Fin.last S.N)) (fun _ => 0) atTop
      (U S (Fin.last S.N)) := by
    refine Normal.tendsto_zero_of_normal (U_open S _) (U_preconn S _) (fun j => (hfamOk j).holo _)
      (fun j z hz => hG_ne0 j _ z hz) (hnorm _) hwdU' ?_
    have hane : (fun j => G j (Fin.last S.N) (wd 0)) = wd := funext fun j => (hfamOk j).anchor
    rw [hane]; exact hwdTend
  have hconvAll : ∀ i : Fin (S.N + 1),
      TendstoLocallyUniformlyOn (fun j => G j i) (fun _ => 0) atTop (U S i) := by
    have key : ∀ t : ℕ, ∀ (ht : t ≤ S.N),
        TendstoLocallyUniformlyOn (fun j => G j (⟨S.N - t, by omega⟩ : Fin (S.N + 1)))
          (fun _ => 0) atTop (U S (⟨S.N - t, by omega⟩ : Fin (S.N + 1))) := by
      intro t
      induction t with
      | zero =>
        intro ht
        have hidx : (⟨S.N - 0, by omega⟩ : Fin (S.N + 1)) = Fin.last S.N := by
          ext; simp
        rw [hidx]
        exact hconvTop
      | succ t ih =>
        intro ht
        have ht' : t ≤ S.N := by omega
        have hcur := ih ht'
        set k : Fin S.N := ⟨S.N - 1 - t, by omega⟩ with hk
        have hsucc : (⟨S.N - t, by omega⟩ : Fin (S.N + 1)) = k.succ := by
          ext; simp [hk, Fin.val_succ]; omega
        have hcast : k.castSucc = (⟨S.N - (t + 1), by omega⟩ : Fin (S.N + 1)) := by
          ext; simp [hk, Fin.val_castSucc]; omega
        have hcur' : TendstoLocallyUniformlyOn (fun j => G j k.succ) (fun _ => 0) atTop (U S k.succ) := by
          rw [← hsucc]; exact hcur
        have hprop := Normal.tendsto_zero_propagate (U_open S k.castSucc) (U_preconn S k.castSucc)
          (U_open S k.succ) (U_inter_nonempty S k) (fun j => (hfamOk j).holo _) (fun j => (hfamOk j).holo _)
          (fun j z hz => hG_ne0 j _ z hz) (fun j z hz => hG_ne0 j _ z hz)
          (hnorm _) (hnorm _) (fun j => (hfamOk j).compat k) hcur'
        rw [hcast] at hprop
        exact hprop
    intro i
    have hidx : (⟨S.N - (S.N - i.val), by omega⟩ : Fin (S.N + 1)) = i := by
      ext; simp; omega
    have h := key (S.N - i.val) (by omega)
    rw [hidx] at h
    exact h
  have hwa_tend : Tendsto wa atTop (𝓝 0) := by
    have hG0t : Tendsto (fun j => G j 0 w₁) atTop (𝓝 0) := by
      have h := (hconvAll 0).tendsto_at hwnU
      simpa using h
    have hev : wa =ᶠ[atTop] fun k => G (k - 1) 0 w₁ := by
      filter_upwards [eventually_ge_atTop 1] with k hk
      simp only [wa, if_neg (by omega : ¬ (k = 0))]
    exact Filter.Tendsto.congr' hev.symm (hG0t.comp tendsto_sub_one_atTop)
  have hwb_tend : Tendsto wb atTop (𝓝 0) := by
    have hGib : Tendsto (fun j => G j ib w₁') atTop (𝓝 0) := by
      have h := (hconvAll ib).tendsto_at hwmU
      simpa using h
    have hev : wb =ᶠ[atTop] fun k => G (k - 1) ib w₁' := by
      filter_upwards [eventually_ge_atTop 1] with k hk
      simp only [wb, if_neg (by omega : ¬ (k = 0))]
    exact Filter.Tendsto.congr' hev.symm (hGib.comp tendsto_sub_one_atTop)
  ------------------------------------------------------------------
  -- the remaining properties of the two sequences
  ------------------------------------------------------------------
  have hwa_ne0 : ∀ j, wa (j + 1) ≠ 0 := by
    intro j
    rw [hwa1 j]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [show G 0 (0 : Fin (S.N + 1)) w₁ = w₁ from by rw [hG0id]; rfl]; exact hw₁ne0
    · exact hG_ne0 j 0 w₁ hwnU
  have hwa_K : ∀ j, wa j ∉ Kset d hd := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hwa0]; exact hw₀K
    · rw [show wa j = G (j - 1) 0 w₁ from by simp only [wa, if_neg (by omega : ¬ (j = 0))]]
      exact (hfamOk (j - 1)).Kfree 0 w₁ hwnU
  have hwa_dom : ∀ j, wa (j + 1) ∈ gdom d hd := by
    intro j
    rw [hwa1 j]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [show G 0 (0 : Fin (S.N + 1)) w₁ = w₁ from by rw [hG0id]; rfl]; exact hw₁mem
    · exact (hfamOk j).dom 0 w₁ hwnU hj
  have hwa_piJ : ∀ j, wa (j + 1) ∈ piExp '' (hd.Bu ∪ hd.Bl) := by
    intro j
    rcases Set.mem_insert_iff.mp (hwa_dom j) with h | h
    · exact absurd h (hwa_ne0 j)
    · exact h
  have hwa_ncrit : ∀ j, deriv (g d) (wa (j + 1)) ≠ 0 := by
    intro j
    refine Deriv.deriv_ne_zero (d := d) hd (fun w hw hk => E_deriv_ne_zero hd hw hk) (hwa_dom j) ?_
    rw [hwa_orbit j]
    exact fun h => hwa_K j (h ▸ critVal_mem_Kset d hd)
  have hwb_ne0 : ∀ j, wb (j + 1) ≠ 0 := by
    intro j
    rw [hwb1 j]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [show G 0 (ib : Fin (S.N + 1)) w₁' = w₁' from by rw [hG0id]; rfl]
      intro h
      rw [h, g_zero] at hgw₁'
      exact hw₀ne hgw₁'.symm
    · exact hG_ne0 j ib w₁' hwmU
  have hwb_K : ∀ j, wb j ∉ Kset d hd := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hwb0]; exact hw₀K
    · rw [show wb j = G (j - 1) ib w₁' from by simp only [wb, if_neg (by omega : ¬ (j = 0))]]
      exact (hfamOk (j - 1)).Kfree ib w₁' hwmU
  have hwb_dom : ∀ j, wb (j + 1) ∈ gdom d hd := by
    intro j
    rw [hwb1 j]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [show G 0 (ib : Fin (S.N + 1)) w₁' = w₁' from by rw [hG0id]; rfl]; exact hw₁'mem
    · exact (hfamOk j).dom ib w₁' hwmU hj
  have hwb_piJ : ∀ j, wb (j + 1) ∈ piExp '' (hd.Bu ∪ hd.Bl) := by
    intro j
    rcases Set.mem_insert_iff.mp (hwb_dom j) with h | h
    · exact absurd h (hwb_ne0 j)
    · exact h
  have hwb_ncrit : ∀ j, deriv (g d) (wb (j + 1)) ≠ 0 := by
    intro j
    refine Deriv.deriv_ne_zero (d := d) hd (fun w hw hk => E_deriv_ne_zero hd hw hk) (hwb_dom j) ?_
    rw [hwb_orbit j]
    exact fun h => hwb_K j (h ▸ critVal_mem_Kset d hd)
  ------------------------------------------------------------------
  -- the two sequences are disjoint away from `w₀`
  ------------------------------------------------------------------
  have hwa_iter : ∀ j k, k ≤ j → (g d)^[k] (wa j) = wa (j - k) := by
    intro j k hk
    induction k with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih (by omega), show j - n = (j - (n + 1)) + 1 by omega,
        hwa_orbit]
  have hwb_iter : ∀ j k, k ≤ j → (g d)^[k] (wb j) = wb (j - k) := by
    intro j k hk
    induction k with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih (by omega), show j - n = (j - (n + 1)) + 1 by omega,
        hwb_orbit]
  have hdisj_ab : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → wa i ≠ wb j := by
    intro i j hi hj h
    rcases le_total i j with hij | hji
    · have hw1 : w₁ = wb (j - (i - 1)) := by
        have h1 : w₁ = (g d)^[i - 1] (wa i) := by
          rw [show wa i = G (i - 1) 0 w₁ from by
            simp only [wa, if_neg (by omega : ¬ (i = 0))]]
          exact ((hfamOk (i - 1)).abel 0 w₁ hwnU).symm
        rw [h1, h, hwb_iter j (i - 1) (by omega)]
      have hw1'eq : w₁' = (g d)^[j - i] w₁ := by
        rw [hw1]
        rw [hwb_iter (j - (i - 1)) (j - i) (Nat.sub_le_sub_left (Nat.sub_le i 1) j)]
        have hidx : (j - (i - 1)) - (j - i) = 1 := by
          have h1 : j - (i - 1) = (j - i) + 1 := by omega
          rw [h1, Nat.add_comm, Nat.add_sub_cancel]
        rw [hidx, hwb1 0, show G 0 ib w₁' = w₁' from by rw [hG0id]; rfl]
      have hcontra : w₁' ∈ Per := by
        rcases Nat.eq_zero_or_pos (j - i) with h0 | hpos
        · rw [h0] at hw1'eq
          simp at hw1'eq
          exact (hne' hw1'eq.symm).elim
        · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
          rw [hm] at hw1'eq
          have h3 : w₁' = (g d)^[m] w₀ := by
            rw [hw1'eq, Function.iterate_succ_apply, hgw₁]
          have h4 : (g d)^[m + 1] w₀ = w₀ := by
            rw [Function.iterate_succ_apply', ← h3, hgw₁']
          refine ⟨m + 1, by omega, ?_⟩
          rw [h3]
          have hcomm : (g d)^[m + 1] ((g d)^[m] w₀) = (g d)^[m] ((g d)^[m + 1] w₀) := by
            rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]
          rw [hcomm, h4]
      exact hw₁'per hcontra
    · have hw1' : w₁' = wa (i - (j - 1)) := by
        have h1 : w₁' = (g d)^[j - 1] (wb j) := by
          rw [show wb j = G (j - 1) ib w₁' from by
            simp only [wb, if_neg (by omega : ¬ (j = 0))]]
          exact ((hfamOk (j - 1)).abel ib w₁' hwmU).symm
        rw [h1, ← h, hwa_iter i (j - 1) (by omega)]
      have hw1eq : w₁ = (g d)^[i - j] w₁' := by
        rw [hw1']
        rw [hwa_iter (i - (j - 1)) (i - j) (Nat.sub_le_sub_left (Nat.sub_le j 1) i)]
        have hidx : (i - (j - 1)) - (i - j) = 1 := by
          have h1 : i - (j - 1) = (i - j) + 1 := by omega
          rw [h1, Nat.add_comm, Nat.add_sub_cancel]
        rw [hidx, hwa1 0, show G 0 (0 : Fin (S.N + 1)) w₁ = w₁ from by rw [hG0id]; rfl]
      have hcontra : w₁ ∈ Per := by
        rcases Nat.eq_zero_or_pos (i - j) with h0 | hpos
        · rw [h0] at hw1eq
          simp at hw1eq
          exact (hne' hw1eq).elim
        · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
          rw [hm] at hw1eq
          have h3 : w₁ = (g d)^[m] w₀ := by
            rw [hw1eq, Function.iterate_succ_apply, hgw₁']
          have h4 : (g d)^[m + 1] w₀ = w₀ := by
            rw [Function.iterate_succ_apply', ← h3, hgw₁]
          refine ⟨m + 1, by omega, ?_⟩
          rw [h3]
          have hcomm : (g d)^[m + 1] ((g d)^[m] w₀) = (g d)^[m] ((g d)^[m + 1] w₀) := by
            rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]
          rw [hcomm, h4]
      exact hw₁per hcontra
  exact ⟨wa, wb, hwa0, hwb0, fun j => ⟨hwa_piJ j, hwa_orbit j, hwa_ncrit j⟩,
    fun j => ⟨hwb_piJ j, hwb_orbit j, hwb_ncrit j⟩, hwa_tend, hwb_tend, hdisj_ab⟩

end
end Work.L61

