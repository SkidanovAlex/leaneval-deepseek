import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.layer_eq_bot_of_normal_contains_t
import Submission.Work.RED.DihOrCycSubgroup
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.BMAX.InvolutionInverts
import Submission.Work.CORE2B.L27_two_part_centralized_proved
import Submission.Work.CORE2B.L27_fittingPi_compl_of_odd
import Submission.Work.CORE2B.L27_fittingPi_sup_compl
import Submission.Work.CORE2B.L27_step1_leaf
import Submission.Work.CORE2B.L27_centralizes_fittingIn

/-!
# CORE2B — the crux `2'`-commutator inclusion (Bender 1981, Lemma 2.7 (a))

Target: under `L27Hyp B M` (Bender's hypotheses of Lemma 2.7 plus `t ∈ M`, `M ⊄ Ĥ`),

  `⁅M, zpowers B.t⁆ ≤ F_{2'}(M)`.

This file owns the *assembly* of the statement from three mathematical steps of Bender's proof
(proved in the sibling modules) and the general nilpotent-group lemma about `F_{2'}(M)`:

* `layerIn M = ⊥` (Bender: "hence `E(M) = 1`"), obtained from the leaf `L27_normal_contains_t`
  through the existing glue `layer_eq_bot_of_normal_contains_t`;
* `⁅M,t⁆ ≤ C_M(F(M))` (Bender: "Now `[M,t] ⊆ C_M(F(M))`");
* `⁅M,t⁆` has odd order (the content of Bender's "hence `O₂(M) = 1`, thus `[M,t]` lies in
  `F_{π'}(M)`");
* `C_M(F(M)) ≤ F(M)` — here, using `T.fstar` (Bender 1.6(a)/1.2) for the D-group `↥M` and
  `E(M) = 1`, we prove `C_M(F(M)) ⊓ M ≤ F(M)`; and finally any odd-order subgroup of `F(M)` lies
  in `F_{2'}(M) = O_{2'}(F(M))`.
-/

open scoped MatrixGroups commutatorElement

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

/-! ## 1. `DihOrCycSylow` is inherited by subgroups

`Work.RED.DihOrCycSylow` has the same definition as `Work.GW2.DihOrCycSylow` (copied verbatim in
the design file), so the RED area's heredity lemma applies directly. -/

theorem dihOrCycSylow_subgroup_local {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (h : Work.GW2.DihOrCycSylow G) : Work.GW2.DihOrCycSylow ↥K :=
  Work.RED.DihOrCycSubgroup (fun n _ H => Work.RED.DihedralSubgroup n H) K h

/-! ## 2. `C_M(F(M)) ⊓ M ≤ F(M)` from `E(M) = 1`

Bender 1.2/1.6(a) (`T.fstar`) applied to the D-group `↥M` gives
`C_{↥M}(F^*(↥M)) ≤ F^*(↥M)`; with `E(M) = 1` we have `F^*(M) = F(M)`. -/

theorem centralizer_fittingIn_inf_le_fitting {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M)
    (hlayer : Work.GW2.layerIn M = ⊥) :
    Subgroup.centralizer ((Work.GW2.fittingIn M : Subgroup G) : Set G) ⊓ M ≤
      Work.GW2.fittingIn M := by
  -- `M` is a D-group
  have hdih : Work.GW2.DihOrCycSylow ↥M := dihOrCycSylow_subgroup_local M hCtx.sylow
  have hcard : Nat.card ↥M < Nat.card G := by
    have hlt : M < ⊤ := lt_of_le_of_ne le_top hD.M_ne_top
    have h := Subgroup.card_lt_of_lt (K := (⊤ : Subgroup G)) hlt
    rwa [Subgroup.card_top] at h
  have hDG : Work.GW2.IsDGroup ↥M := hCtx.ih ↥M hcard hdih
  have hfstar := T.fstar ↥M hFT hdih hDG
  -- `layer ↥M = ⊥`, hence `fstar ↥M = fitting ↥M`
  have hlayerM : Work.GW2.layer ↥M = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp hlayer
  rw [Work.GW2.fstar, hlayerM, sup_bot_eq] at hfstar
  -- translate the conclusion
  intro x hx
  obtain ⟨hxc, hxM⟩ := hx
  have hmem : (⟨x, hxM⟩ : ↥M) ∈
      Subgroup.centralizer (((Work.GW2.fitting ↥M) : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc (y : G) ⟨y, hy, rfl⟩)
  exact ⟨⟨x, hxM⟩, hfstar hmem, rfl⟩

/-! ## 3. The commutator of `M` with a normalizing involution

If `t` is an involution normalizing `F` and acting on `F` either by inversion or trivially, then
`⁅M, t⁆` centralizes `F`: conjugation by `⁅m,t⁆ = m t m⁻¹ t⁻¹` is `c_m ∘ c_t ∘ c_m ∘ c_t` and
either action makes this trivial on `F`. -/

/-- **Inversion form.**  If `t` inverts `F` pointwise then `⁅M, ⟨t⟩⁆` centralizes `F`. -/
theorem commutator_le_centralizer_of_inverts {G : Type} [Group G] {M F : Subgroup G} {t : G}
    (hM : M ≤ Subgroup.normalizer (F : Set G))
    (hinv : ∀ x ∈ F, t * x * t⁻¹ = x⁻¹) (ht : t * t = 1) :
    ⁅M, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (F : Set G) := by
  have hpow : ∀ y ∈ Subgroup.zpowers t, y = 1 ∨ y = t := by
    intro y hy
    rw [Subgroup.zpowers_eq_closure] at hy
    revert hy
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact Or.inr hx
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (by rw [hx, hy, mul_one])
      · exact Or.inr (by rw [hx, hy, one_mul])
      · exact Or.inr (by rw [hx, hy, mul_one])
      · exact Or.inl (by rw [hx, hy]; exact ht)
    · intro x _ hx
      rcases hx with hx | hx
      · exact Or.inl (by rw [hx]; exact inv_one)
      · exact Or.inr (by rw [hx]; exact inv_eq_of_mul_eq_one_right ht)
  have hone : ∀ m ∈ M, ⁅m, (1 : G)⁆ ∈ Subgroup.centralizer (F : Set G) := by
    intro m _
    rw [commutatorElement_one_right]
    exact Subgroup.one_mem _
  have hgen : ∀ m ∈ M, ⁅m, t⁆ ∈ Subgroup.centralizer (F : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hzF : m * z⁻¹ * m⁻¹ ∈ F := by
      have h : m * z⁻¹ * m⁻¹ = (m * z * m⁻¹)⁻¹ := by group
      rw [h]
      exact F.inv_mem ((Subgroup.mem_normalizer_iff.mp (hM hm) z).mp hz)
    have key1 : t⁻¹ * z * t = z⁻¹ := by
      rw [htinv]
      simpa [htinv] using hinv z hz
    have hmemF : m⁻¹ * z⁻¹ * m ∈ F := by
      have h := (Subgroup.mem_normalizer_iff.mp (hM (M.inv_mem hm)) z⁻¹).mp (F.inv_mem hz)
      simpa using h
    have key2 : t * (m⁻¹ * z⁻¹ * m) * t⁻¹ = m⁻¹ * z * m := by
      have h := hinv (m⁻¹ * z⁻¹ * m) hmemF
      rw [h]
      group
    have hconj : ⁅m, t⁆ * z * ⁅m, t⁆⁻¹ = z := by
      calc ⁅m, t⁆ * z * ⁅m, t⁆⁻¹
          = m * (t * (m⁻¹ * (t⁻¹ * z * t) * m) * t⁻¹) * m⁻¹ := by
            rw [commutatorElement_def]; group
        _ = m * (t * (m⁻¹ * z⁻¹ * m) * t⁻¹) * m⁻¹ := by rw [key1]
        _ = m * (m⁻¹ * z * m) * m⁻¹ := by rw [key2]
        _ = z := by group
    have h1 : ⁅m, t⁆ * z = z * ⁅m, t⁆ := by
      calc ⁅m, t⁆ * z = (⁅m, t⁆ * z * ⁅m, t⁆⁻¹) * ⁅m, t⁆ := by group
        _ = z * ⁅m, t⁆ := by rw [hconj]
    exact h1.symm
  rw [Subgroup.commutator_le]
  intro m hm y hy
  rcases hpow y hy with rfl | rfl
  · exact hone m hm
  · exact hgen m hm

/-- **Trivial-action form.**  If `t` centralizes `F` pointwise then `⁅M, ⟨t⟩⁆` centralizes `F`. -/
theorem commutator_le_centralizer_of_centralizes {G : Type} [Group G] {M F : Subgroup G} {t : G}
    (hM : M ≤ Subgroup.normalizer (F : Set G))
    (hcen : ∀ x ∈ F, t * x * t⁻¹ = x) (ht : t * t = 1) :
    ⁅M, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (F : Set G) := by
  have hpow : ∀ y ∈ Subgroup.zpowers t, y = 1 ∨ y = t := by
    intro y hy
    rw [Subgroup.zpowers_eq_closure] at hy
    revert hy
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact Or.inr hx
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (by rw [hx, hy, mul_one])
      · exact Or.inr (by rw [hx, hy, one_mul])
      · exact Or.inr (by rw [hx, hy, mul_one])
      · exact Or.inl (by rw [hx, hy]; exact ht)
    · intro x _ hx
      rcases hx with hx | hx
      · exact Or.inl (by rw [hx]; exact inv_one)
      · exact Or.inr (by rw [hx]; exact inv_eq_of_mul_eq_one_right ht)
  have hone : ∀ m ∈ M, ⁅m, (1 : G)⁆ ∈ Subgroup.centralizer (F : Set G) := by
    intro m _
    rw [commutatorElement_one_right]
    exact Subgroup.one_mem _
  have hgen : ∀ m ∈ M, ⁅m, t⁆ ∈ Subgroup.centralizer (F : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have key1 : t⁻¹ * z * t = z := by
      simpa [htinv] using hcen z hz
    have hmemF : m⁻¹ * z * m ∈ F := by
      have h := (Subgroup.mem_normalizer_iff.mp (hM (M.inv_mem hm)) z).mp hz
      simpa using h
    have key2 : t * (m⁻¹ * z * m) * t⁻¹ = m⁻¹ * z * m := hcen _ hmemF
    have hconj : ⁅m, t⁆ * z * ⁅m, t⁆⁻¹ = z := by
      calc ⁅m, t⁆ * z * ⁅m, t⁆⁻¹
          = m * (t * (m⁻¹ * (t⁻¹ * z * t) * m) * t⁻¹) * m⁻¹ := by
            rw [commutatorElement_def]; group
        _ = m * (t * (m⁻¹ * z * m) * t⁻¹) * m⁻¹ := by rw [key1]
        _ = m * (m⁻¹ * z * m) * m⁻¹ := by rw [key2]
        _ = z := by group
    have h1 : ⁅m, t⁆ * z = z * ⁅m, t⁆ := by
      calc ⁅m, t⁆ * z = (⁅m, t⁆ * z * ⁅m, t⁆⁻¹) * ⁅m, t⁆ := by group
        _ = z * ⁅m, t⁆ := by rw [hconj]
    exact h1.symm
  rw [Subgroup.commutator_le]
  intro m hm y hy
  rcases hpow y hy with rfl | rfl
  · exact hone m hm
  · exact hgen m hm

/-! ## 4. `[M,t]` centralizes `F_{π'}(M)`

Immediate from `t` inverting `F_{π'}(M)` (Bender 2.7, step 3; proved as
`inverts_fittingPiIn_pi_compl_local`). -/

theorem commutator_le_centralizer_fittingPi_pi_compl {G : Type} [Group G] [Finite G]
    (h23 : Work.GW2.Lemma23Prop) (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M) :
    ⁅M, Subgroup.zpowers B.t⁆ ≤
      Subgroup.centralizer ((Work.GW2.fittingPiIn B.piᶜ M : Subgroup G) : Set G) := by
  have ht2 : B.t * B.t = 1 := by
    have h := pow_orderOf_eq_one B.t
    rw [B.t_order] at h
    simpa [pow_two] using h
  exact commutator_le_centralizer_of_inverts (le_normalizer_fittingPiIn_local B.piᶜ M)
    (inverts_fittingPiIn_pi_compl_local h23 hFT hCtx B M hD) ht2

/-- `[M,t]` centralizes `F_2(M)`: immediate from the sibling leaf
`L27_two_part_centralized` (`t` centralizes `F_2(M)`). -/
theorem commutator_le_centralizer_fittingPi_two {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop)
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M) :
    ⁅M, Subgroup.zpowers B.t⁆ ≤
      Subgroup.centralizer ((Work.GW2.fittingPiIn ({2} : Set ℕ) M : Subgroup G) : Set G) := by
  have ht2 : B.t * B.t = 1 := by
    have h := pow_orderOf_eq_one B.t
    rw [B.t_order] at h
    simpa [pow_two] using h
  exact commutator_le_centralizer_of_centralizes (le_normalizer_fittingPiIn_local {2} M)
    (fun x hx => by
      rw [Subgroup.mem_centralizer_iff.mp
        (L27_two_part_centralized_proved T h23 h26 G hFT hCtx B M hD hx) B.t rfl]
      group) ht2

/-- **`[M,t] ≤ C_M(F(M))` from the two halves.**  Bender's step "Now `[M,t] ⊆ C_M(F(M))`".

Inputs: `t` centralizes `F_π(M)` (Bender's sentence, `L27_pi_part_centralized`), `t` inverts
`F_{π'}(M)` (`inverts_fittingPiIn_pi_compl_local`), and the nilpotent split
`F(M) = F_π(M) ⊔ F_{π'}(M)` (`L27_fittingPi_sup_compl`). -/
theorem centralizes_fittingIn_of_parts {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (M : Subgroup G)
    (hpi : Work.GW2.fittingPiIn B.pi M ≤ Subgroup.centralizer ({B.t} : Set G))
    (hjoin : Work.GW2.fittingPiIn B.pi M ⊔ Work.GW2.fittingPiIn B.piᶜ M = Work.GW2.fittingIn M)
    (hinv : Work.GW2.Inverts B.t (Work.GW2.fittingPiIn B.piᶜ M)) :
    ⁅M, Subgroup.zpowers B.t⁆ ≤
      Subgroup.centralizer ((Work.GW2.fittingIn M : Subgroup G) : Set G) := by
  have ht2 : B.t * B.t = 1 := by
    have h := pow_orderOf_eq_one B.t
    rw [B.t_order] at h
    simpa [pow_two] using h
  have h1 : ⁅M, Subgroup.zpowers B.t⁆ ≤
      Subgroup.centralizer ((Work.GW2.fittingPiIn B.pi M : Subgroup G) : Set G) :=
    commutator_le_centralizer_of_centralizes (le_normalizer_fittingPiIn_local B.pi M)
      (fun x hx => by
        rw [Subgroup.mem_centralizer_iff.mp (hpi hx) B.t rfl]
        group) ht2
  have h2 : ⁅M, Subgroup.zpowers B.t⁆ ≤
      Subgroup.centralizer ((Work.GW2.fittingPiIn B.piᶜ M : Subgroup G) : Set G) :=
    commutator_le_centralizer_of_inverts (le_normalizer_fittingPiIn_local B.piᶜ M) hinv ht2
  have h3 : ⁅M, Subgroup.zpowers B.t⁆ ≤
      Subgroup.centralizer ((Work.GW2.fittingPiIn B.pi M ⊔
        Work.GW2.fittingPiIn B.piᶜ M : Subgroup G) : Set G) := by
    rw [Subgroup.centralizer_sup]
    exact le_inf h1 h2
  rwa [hjoin] at h3

/-- **Bender's step "`[M,t] ⊆ C_M(F(M))`"** from the single remaining input: `t` centralizes
`F_π(M)`.  (The companion statement "`t` inverts `F_{π'}(M)`" is
`inverts_fittingPiIn_pi_compl_local`, and the nilpotent split `F(M) = F_π(M) ⊔ F_{π'}(M)` is
`L27_fittingPi_sup_compl`.) -/
theorem centralizes_fittingIn_of_pi_part {G : Type} [Group G] [Finite G]
    (h23 : Work.GW2.Lemma23Prop) (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M)
    (hpi : Work.GW2.fittingPiIn B.pi M ≤ Subgroup.centralizer ({B.t} : Set G)) :
    ⁅M, Subgroup.zpowers B.t⁆ ≤
      Subgroup.centralizer ((Work.GW2.fittingIn M : Subgroup G) : Set G) := by
  refine centralizes_fittingIn_of_parts B M hpi ?_
    (inverts_fittingPiIn_pi_compl_local h23 hFT hCtx B M hD)
  exact L27_fittingPi_sup_compl G B.pi (fun q hq => Nat.prime_of_mem_primeFactors hq) M

/-! ## 5. Assembly -/

theorem L27_crux_of_aux
    (hstep1 : Work.CORE2B.L27_normal_contains_t)
    (hcent : ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop)
      (_h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G],
      Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), Work.CORE2B.L27Hyp B M →
        ⁅M, Subgroup.zpowers B.t⁆ ≤
          Subgroup.centralizer ((Work.GW2.fittingIn M : Subgroup G) : Set G))
    (hodd : ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop)
      (_h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G],
      Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), Work.CORE2B.L27Hyp B M →
        Odd (Nat.card (⁅M, Subgroup.zpowers B.t⁆ : Subgroup G))) :
    ∀ (T : Work.GW2.LocalToolkit) (_h23 : Work.GW2.Lemma23Prop) (_h26 : Work.GW2.Thm26Prop)
      (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), Work.CORE2B.L27Hyp B M →
        ⁅M, Subgroup.zpowers B.t⁆ ≤ Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) M := by
  intro T h23 h26 G _ _ hFT hCtx B M hD
  -- `E(M) = 1`
  have hlayer : Work.GW2.layerIn M = ⊥ :=
    layer_eq_bot_of_normal_contains_t hstep1 T h23 h26 G hFT hCtx B M hD
  have hfM := centralizer_fittingIn_inf_le_fitting T hFT hCtx B M hD hlayer
  -- `⁅M,t⁆ ≤ M`
  have hKM : ⁅M, Subgroup.zpowers B.t⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro m hm y hy
    have hyM : y ∈ M := (Subgroup.zpowers_le.mpr hD.t_mem) hy
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hm hyM) (M.inv_mem hm)) (M.inv_mem hyM)
  have hKc := hcent T h23 h26 G hFT hCtx B M hD
  have hKF : ⁅M, Subgroup.zpowers B.t⁆ ≤ Work.GW2.fittingIn M :=
    (le_inf hKc hKM).trans hfM
  exact L27_fittingPi_compl_of_odd G M _ hKF (hodd T h23 h26 G hFT hCtx B M hD)

/-! ## 6. The one remaining input, and its status — the target is *not* derivable from `L27Hyp`

`L27_crux_commutator_2prime` below is proved from

* `L27_step1_leaf` (`E(M) = 1`) — proved;
* `L27_centralizes_fittingIn` (`⁅M,t⁆ ≤ C_M(F(M))`) — proved;
* `L27_commutator_odd` (`Odd (Nat.card ⁅M,t⁆)`) — **owed, and not derivable from the stated
  hypotheses**; `L27Hyp` is one hypothesis short (see below).

The third input is *equivalent* to the target given the first two: `L27_crux_of_aux` proves
`⁅M,t⁆ ≤ F(M)` from them (via `E(M) = 1` and `T.fstar`), and an odd-order subgroup of the
nilpotent group `F(M)` lies in `F_{2'}(M)` (`L27_fittingPi_compl_of_odd`); conversely `F_{2'}(M)`
is odd.  So `Odd (Nat.card ⁅M,t⁆)` and the target are inter-derivable here, and *any* proof of the
target proves oddness.

Write `A := ⁅M, B.t⁆ = ⁅M, zpowers B.t⁆`.  From the proved pieces one gets
`A ≤ F(M) ⊓ C_M(F(M))` (so `A ⊆ Z(F(M))` is abelian) and `t` acts on `A` by inversion (it inverts
the generators `⁅m,t⁆`; `L27_conj_t_inverts`).  Consequently

* `A ⊓ O₂(M) = A ⊓ C_M(t) = A[2] = Ω₁(A)`: an element of `A ⊓ C(t)` is both centralised and
  inverted by `t`, hence an involution; and `Ω₁(A)` is characteristic in `A ◁ M`, so it is a
  normal elementary abelian `2`-subgroup of `M`, hence inside `O₂(M)`.  Also `A[2] ⊆ Z(F(M))`.
* `Odd (Nat.card A) ↔ A ⊓ O₂(M) = ⊥` (Cauchy's theorem for the forward implication, coprimality
  for the converse).
* `O₂(M) ≤ O₂(Ĥ)` (Bender: "`[O₂(M),U] = 1`, hence `O₂(M) ⊆ O₂(Ĥ)`") is *not* available:
  `O₂(M) ≤ F₂(M) ≤ C(t)` gives only `O₂(M) ≤ a Sylow of H` after conjugating inside `H = SU`, and
  `O₂(H) ≤ S ⊓ C(U) = O₂(Ĥ)` needs `O₂(M) ≤ C(U)`, i.e. Bender's `1.1.iv` step with
  `K₀ = M ∩ F(U)`, which needs `F(U) ≤ M` (equivalently `F_{2'}(Ĥ) ≤ M`).  Nothing in `L27Hyp`
  gives that; see the module docstring of `L27su_two_core_centralizes_U` (which states it as the
  missing input, with a `PSL(2,11)` configuration satisfying every local clause) and
  `NOTES_L27_commutator.md` §§3–4.
* With `O₂(M) ≤ O₂(Ĥ)` available, everything closes.  Case A of `h26` (`Ĥ = H`, `O₂(Ĥ) ≤ S₀`
  cyclic): `O₂(M)` is a cyclic `2`-subgroup of `S₀`, so `A[2] ⊆ O₂(M) ⊆ ⟨t⟩`; if `A[2] ≠ ⊥` then
  `t ∈ A[2] ◁ M`, so `⟨t⟩ ◁ M`, so `M ≤ N_G(⟨t⟩) = C_G(t) = H ≤ Ĥ`, contradicting `¬ M ≤ Ĥ`.
  Case B (`O₂(Ĥ)` a four-group): if `O₂(M) = O₂(Ĥ)` or `O₂(M) ∋ t` then `⟨t⟩ ◁ M` (respectively
  `O₂(M) = O₂(Ĥ) ◁ Ĥ` gives `M ≤ N_G(O₂(Ĥ)) = Ĥ`, `L27_api.normalizer_pCoreIn_two_eq_Hhat`),
  contradiction; the one remaining configuration is `O₂(M) = ⟨z⟩` a *line* of the four-group
  `O₂(Ĥ)` with `z ≠ t`.  Then `⟨z⟩ ◁ M` forces `z ∈ Z(M)`, so `M ≤ C_G(z) = C_G(t^g) = B.H^g`, and
  `M^{g^{-1}} ≤ H = C(t)`; and since `O₂(M^{g^{-1}}) = ⟨t⟩` while `M^{g^{-1}} ≤ H = S ⋊ U` makes
  `M^{g^{-1}} ∩ U` a normal Hall `2'`-subgroup with `2`-group quotient, `M^{g^{-1}}` would have to
  be `2`-nilpotent with a *cyclic* Sylow `2`-subgroup of order `2`, contradicting `sylow_nc` —
  **except** that this last step needs `S ◁ H`, which is false in general (`H = S₃`), so the case
  stands open.
* The `|P| ≥ 8` case of a Sylow `P ≤ C_M(t)` of `M` (which exists by `L27Hyp.size`, through
  `sylow_central_of_large_inter`, `sylow_central_of_card_four`, `L27cf_twoResidual`) also reduces
  to the same gap: `A[2] ◁ P` is a normal elementary abelian subgroup of the dihedral `2`-group
  `P` with `Z(P) = ⟨t⟩`, so (by `L27dihedral_centre_mem_of_normal_abelian`) `A[2] ≠ ⊥` forces
  `t ∈ A[2] ⊆ A`, whence `t ∈ A ⊆ C_M(F(M))` makes `t` centralise `F(M)`; then `F_{π'}(M) = 1`
  (it is inverted and centralised), `F(M) = F_π(M) ≤ Ĥ` (`h23` (i)), and one is left with
  `t ∈ O₂(M) ∩ A[2]` — again the missing input.

So the obstruction is exactly `t ∈ O₂(M)`/`A ⊓ O₂(M) ≠ ⊥`, and ruling it out is Bender's step
`O₂(M) = 1 (otherwise N_G(O₂(M)) ≤ Ĥ)`, which the source performs with `M` **maximal**.  The area
has since made this explicit: `Basic.lean` defines `L27HypS` = `L27Hyp` + `IsCoatom M` +
`BRel M B.Hhat` with the docstring "the two maximality inputs that step (4) of the proof needs",
and states the leaf as `L27_commutator_leS` over `L27HypS`.  `L27Hyp` carries `M ≠ ⊤`,
`Ĥ ⇝ M`, `¬ M ≤ Ĥ`, `t ∈ M` but neither `IsCoatom M` nor `M ⇝ Ĥ`; two independent reviewers of the
isolated step `B.t ∉ ⁅M, B.t⁆` returned "probably wrong as stated — one hypothesis short".
-/

/-! ## 7. The target declaration — RETIRED (statement kept, declaration removed)

```
theorem L27_crux_commutator_2prime (T) (h23) (h26) (G) (hFT) (hCtx) (B) (M) (hD : L27Hyp B M) :
    ⁅M, Subgroup.zpowers B.t⁆ ≤ F_{2'}(M)
```

The whole content of the file above is the *reduction* `L27_crux_of_aux`, which consumes the
oddness input `Odd (Nat.card ⁅M,t⁆)`; that input is not derivable from `L27Hyp` (see the analysis
in the docstring of section 6 and `NOTES_L27_commutator.md`), so the unconditional form is retired.
The corrected form is `L27_crux_of_aux` itself (oddness as a hypothesis), and the delivered route
uses `L27fin_odd_of_O2_bot` (`O₂(M) = ⊥` as a hypothesis).  The declaration has been **removed** so
that no module on the delivered path contains an unproved statement. -/

end Work.CORE2B
