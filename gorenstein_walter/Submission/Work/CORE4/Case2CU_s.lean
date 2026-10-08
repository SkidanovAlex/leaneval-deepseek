import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F

namespace Work.CORE4

open Subgroup

/-- **The exact gap in `Case2CU_s`, formalised.**

`Case2CU_s` asks for `B.U ⊓ C_G(s) = (B.U ⊓ M) ⊓ C_G(s)`, i.e. Bender's `§4 (5)` second half
`B = C_U(s)`.  Writing `Y := C_{F(U)}(s) = fittingIn B.U ⊓ C_G(s)`, the statement follows from the
recorded hypotheses **once one adds** Bender's printed first half of `§4 (5)`, i.e. the hypothesis

`M ≤ N_G(Y)`   (equivalently `C_{F(U)}(s) ⊴ M`, equivalently `C_{F(U)}(s) = F`).

(The equivalence with `C_{F(U)}(s) = F` uses `F = (U ⊓ M ⊓ C_G(s)) ⊓ F(U) = Y ⊓ M`, which is a
pure unfolding: `F(U) ≤ U`.)

**Proof.**  `F ≤ Y` by definition of `Y` and `F ≠ ⊥` give `Y ≠ ⊥`; `Y ≤ U ≤ H < ⊤`; hence
`N_G(Y) ≠ ⊤` (if `N_G(Y) = ⊤` then `Y ⊴ G` with `Y ≠ 1` and `Y ≤ H < G`, against the simplicity of
`G`, `hbc.simple`).  As `M` is a coatom with `M ≤ N_G(Y)`, this forces `N_G(Y) = M`, whence
`Y ≤ M`.  Finally, for `u ∈ C_U(s)` one has `u ∈ N_G(Y)`: `u ∈ U` normalises `fittingIn B.U`
(=`F(U) ⊴ U`, since `fitting ↥B.U ⊴ ↥B.U`), and `u` centralises `s`, so it fixes
`Y = fittingIn B.U ⊓ C_G(s)`; therefore `u ∈ N_G(Y) = M`.

**The extra hypothesis is not redundancy.**  Nothing in the recorded hypothesis list relates
`C_U(s)` (or `Y`) to `M`: the `(1)`,`(2)` hypotheses of the statement describe only the
`M`-restricted pieces `K = I_{U⊓M}(s)`, `B₀ = C_{U⊓M}(s)` of `U ⊓ M = K ⊔ B₀`, and `F` is
*defined* with the intersection with `M` built in (`F = Y ⊓ M`).  Bender derives `Y ≤ M` from his
`(4)` together with the structure of `E/Z(E) ∈ {A₇, L₂(q)}` — content which the recorded list does
not contain (see `Case2Setup9F.lean` and `NOTES_CORE4.md`). -/
theorem Case2CU_s_of_normal (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M P : Subgroup G) (s : G),
        IsCoatom M → B.t ∈ Work.GW2.layerIn M → ¬ B.H ≤ M →
        M = Work.GW2.layerIn M ⊔ (M ⊓ B.H) →
        IsPGroup 2 P → P ≤ M ⊓ B.H → ¬ 2 ∣ P.relIndex M →
        s ∈ P ⊓ Work.GW2.layerIn M → orderOf s = 2 →
        (Work.GW2.invSet (B.U ⊓ M) s : Set G) =
            ((⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) : Set G) →
        IsCyclic (⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) →
        ((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) =
            (B.U ⊓ M) ⊓ Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G) →
        B.U ⊓ M = (⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) ⊔
            ((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) →
        (((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ Work.GW2.fittingIn B.U) ≠ ⊥ →
        (((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ Work.GW2.fittingIn B.U) ≤
            Subgroup.centralizer ((Work.GW2.layerIn M : Subgroup G) : Set G) →
        Subgroup.normalizer (((((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓
            Work.GW2.fittingIn B.U) : Subgroup G) : Set G) = M →
        M ≤ Subgroup.normalizer ((((Work.GW2.fittingIn B.U ⊓
            Subgroup.centralizer ({s} : Set G)) : Subgroup G)) : Set G) →
        B.U ⊓ Subgroup.centralizer ({s} : Set G) =
            (B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G) := by
  intro G _ _ hbc B M P s hcoat ht_mem hnotH hM hP2 hPM hPidx hs_mem hs_order hinv hKcyc
    hCs hUeq hFne hFcent hNF hYnorm
  classical
  haveI hsimple : IsSimpleGroup G := hbc.simple
  set Y : Subgroup G := Work.GW2.fittingIn B.U ⊓ Subgroup.centralizer ({s} : Set G) with hY
  -- the extra hypothesis, written with `Y`
  have hYnorm' : M ≤ Subgroup.normalizer (Y : Set G) := hYnorm
  -- `Y ≤ U ≤ H < ⊤`
  have hYU : Y ≤ B.U := by
    rw [hY]
    exact le_trans inf_le_left (Subgroup.map_subtype_le (Work.GW2.fitting ↥B.U))
  have hYH : Y ≤ B.H :=
    le_trans hYU (Subgroup.map_subtype_le (Work.GW2.oddCore ↥B.H))
  have hHlt : B.H < ⊤ := lt_of_le_of_lt B.H_le_Hhat B.Hhat_coatom.lt_top
  -- `F ≤ Y` and `F ≠ ⊥` give `Y ≠ ⊥`
  have hFY : ((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ Work.GW2.fittingIn B.U ≤ Y := by
    rw [hY]
    exact le_inf inf_le_right (le_trans inf_le_left inf_le_right)
  have hYne : Y ≠ ⊥ := by
    intro hbot
    exact hFne (le_bot_iff.mp (hbot ▸ hFY))
  -- `N_G(Y) ≠ ⊤` by simplicity of `G`
  have hNtop : Subgroup.normalizer (Y : Set G) ≠ ⊤ := by
    intro htop
    haveI : Y.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y with h | h
    · exact hYne h
    · have hle : (⊤ : Subgroup G) ≤ B.H := h ▸ hYH
      exact absurd (lt_of_le_of_lt hle hHlt) (lt_irrefl ⊤)
  -- `M` is a coatom normalising `Y`, so `N_G(Y) = M` and `Y ≤ M`
  have hN : Subgroup.normalizer (Y : Set G) = M := by
    rcases eq_or_lt_of_le hYnorm' with h | h
    · exact h.symm
    · exact absurd (hcoat.2 _ h) hNtop
  have hYleM : Y ≤ M := hN ▸ Subgroup.le_normalizer
  -- `u ∈ U` normalises `F(U)`
  have hfit_conj : ∀ w ∈ B.U, ∀ k ∈ Work.GW2.fittingIn B.U,
      w * k * w⁻¹ ∈ Work.GW2.fittingIn B.U := by
    intro w hw k hk
    haveI hfitN : (Work.GW2.fitting ↥B.U).Normal := Subgroup.normalCore_normal _
    obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.mp hk
    rw [← hyk]
    refine Subgroup.mem_map.mpr ⟨(⟨w, hw⟩ : ↥B.U) * y * (⟨w, hw⟩ : ↥B.U)⁻¹, ?_, ?_⟩
    · exact hfitN.conj_mem y hy ⟨w, hw⟩
    · simp [map_mul]
  -- `u ∈ C_G(s)` normalises `C_G(s)`
  have hcent_conj : ∀ w ∈ Subgroup.centralizer ({s} : Set G),
      ∀ k ∈ Subgroup.centralizer ({s} : Set G),
      w * k * w⁻¹ ∈ Subgroup.centralizer ({s} : Set G) := by
    intro w hw k hk
    exact (Subgroup.centralizer ({s} : Set G)).mul_mem
      ((Subgroup.centralizer ({s} : Set G)).mul_mem hw hk)
      ((Subgroup.centralizer ({s} : Set G)).inv_mem hw)
  -- hence every `u ∈ C_U(s)` normalises `Y`
  have hconjY : ∀ w ∈ B.U ⊓ Subgroup.centralizer ({s} : Set G),
      ∀ k ∈ Y, w * k * w⁻¹ ∈ Y := by
    intro w hw k hk
    obtain ⟨hwU, hwC⟩ := Subgroup.mem_inf.mp hw
    rw [hY] at hk
    obtain ⟨hkA, hkC⟩ := Subgroup.mem_inf.mp hk
    exact Subgroup.mem_inf.mpr ⟨hfit_conj w hwU k hkA, hcent_conj w hwC k hkC⟩
  -- the goal
  refine le_antisymm ?_ ?_
  · intro u hu
    obtain ⟨huU, huC⟩ := Subgroup.mem_inf.mp hu
    have huY : u ∈ B.U ⊓ Subgroup.centralizer ({s} : Set G) :=
      Subgroup.mem_inf.mpr ⟨huU, huC⟩
    have huN : u ∈ Subgroup.normalizer (Y : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        exact hconjY u huY h hh
      · intro hh
        have hinv : u⁻¹ ∈ B.U ⊓ Subgroup.centralizer ({s} : Set G) :=
          (B.U ⊓ Subgroup.centralizer ({s} : Set G)).inv_mem huY
        have h2 := hconjY u⁻¹ hinv (u * h * u⁻¹) hh
        have hx : u⁻¹ * (u * h * u⁻¹) * (u⁻¹)⁻¹ = h := by group
        rwa [hx] at h2
    have huM : u ∈ M := hN ▸ huN
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨huU, huM⟩, huC⟩
  · exact le_inf (le_trans inf_le_left inf_le_left) inf_le_right

/-- Fitting's theorem in the form needed here (the area's own proof, `SevenX.PiFU`). -/
theorem isNilpotent_fittingIn_area {G : Type} [Group G] [Finite G] (A : Subgroup G) :
    Group.IsNilpotent ↥(Work.GW2.fittingIn A) :=
  Work.CORE4.SevenX.PiFU.isNilpotent_fittingIn A

/-- In a nilpotent group `Y`, a subgroup `F ≤ Y` with `N_Y(F) ≤ F` is all of `Y`. -/
theorem eq_of_le_of_isNilpotent_of_normalizer {G : Type} [Group G] [Finite G]
    (F Y : Subgroup G) (hFY : F ≤ Y) (hY : Group.IsNilpotent ↥Y)
    (hN : Y ⊓ normalizer (F : Set G) ≤ F) : F = Y := by
  classical
  by_contra hne
  have hlt : F.subgroupOf Y < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm hFY ?_)
    intro y hy
    have : (⟨y, hy⟩ : ↥Y) ∈ F.subgroupOf Y := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have hgrow := Group.normalizerCondition_of_isNilpotent (F.subgroupOf Y) hlt
  obtain ⟨y, hyN, hyF⟩ := IsConcreteLE.exists_of_lt hgrow
  apply hyF
  rw [Subgroup.mem_subgroupOf]
  refine hN (Subgroup.mem_inf.mpr ⟨y.2, ?_⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_normalizer_iff] at hyN
  constructor
  · intro hh
    have := (hyN ⟨h, hFY hh⟩).mp (Subgroup.mem_subgroupOf.mpr hh)
    simpa [Subgroup.mem_subgroupOf] using this
  · intro hh
    have hYh : (y : G) * h * (y : G)⁻¹ ∈ Y := hFY hh
    have hhY : h ∈ Y := by
      have : (y : G)⁻¹ * ((y : G) * h * (y : G)⁻¹) * (y : G) = h := by group
      rw [← this]
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem y.2) hYh) y.2
    have := (hyN ⟨h, hhY⟩).mpr (by simpa [Subgroup.mem_subgroupOf] using hh)
    simpa [Subgroup.mem_subgroupOf] using this

/-- Bender §4 (5), first half: `N_G(F) = M` forces `C_{F(U)}(s) = F`, hence
`M ≤ N_G(C_{F(U)}(s))` — the input that `Case2CU_s_of_normal` consumes.  (Design pass 17 item A.)

Here `F = (U ⊓ M) ⊓ C_G(s) ⊓ F(U)` and `Y = F(U) ⊓ C_G(s)`; `Y` is nilpotent
(`isNilpotent_fittingIn_area`), `F ≤ Y`, and `Y ⊓ N(F) = Y ⊓ M = F` by `N_G(F) = M` and the
definitions, so `eq_of_le_of_isNilpotent_of_normalizer` gives `F = Y`. -/
theorem le_normalizer_CFU_of_normalizer_F {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (s : G)
    (hNF : Subgroup.normalizer (((((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓
            Work.GW2.fittingIn B.U) : Subgroup G) : Set G) = M) :
    M ≤ Subgroup.normalizer ((((Work.GW2.fittingIn B.U ⊓
            Subgroup.centralizer ({s} : Set G)) : Subgroup G)) : Set G) := by
  set F : Subgroup G :=
    ((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ Work.GW2.fittingIn B.U with hF
  set Y : Subgroup G := Work.GW2.fittingIn B.U ⊓ Subgroup.centralizer ({s} : Set G) with hY
  have hFU : Work.GW2.fittingIn B.U ≤ B.U := Subgroup.map_subtype_le _
  have hFY : F ≤ Y := le_inf inf_le_right (le_trans inf_le_left inf_le_right)
  have hYnil : Group.IsNilpotent ↥Y := by
    haveI : Group.IsNilpotent ↥(Work.GW2.fittingIn B.U) := isNilpotent_fittingIn_area B.U
    have hle : Y ≤ Work.GW2.fittingIn B.U := inf_le_left
    exact (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hle)).mp inferInstance
  have hN : Y ⊓ Subgroup.normalizer (F : Set G) ≤ F := by
    rw [hNF]
    intro y hy
    obtain ⟨hyY, hyM⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨hyFU, hyC⟩ := Subgroup.mem_inf.mp hyY
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hFU hyFU, hyM⟩, hyC⟩, hyFU⟩
  have hEq : F = Y := eq_of_le_of_isNilpotent_of_normalizer F Y hFY hYnil hN
  rw [← hEq, hNF]

/-- Bender 1981, §4 (5): `B = C_U(s)`, isolated from the rest of §4 (3)–(5).

TWO REVIEWS of this statement judged it "probably wrong as stated / under-hypothesised" (missing
`F = C_{F(U)}(s)`, i.e. `C_{F(U)}(s) ≤ M`).  The requester asks explicitly for a verdict: either
derive it from the listed hypotheses (the deep structure of the A₇/L₂(q) configuration is
available through `I : C4Inputs`: `I.toolkit.lay`, `I.toolkit.c15`, `I.toolkit.d11*`,
`I.toolkit.l2*`, `I.toolkit.a7`, `I.layerOneInvClass`, `I.lem27`, `I.lem28`, `I.thm26`), or
report precisely which missing hypothesis is needed.

Here `B` is Bender's name for `B₀ := (U ⊓ M) ⊓ C_G(s)`; the statement says `C_U(s) ⊆ M`, i.e.
`B.U ⊓ C_G(s) = (B.U ⊓ M) ⊓ C_G(s)`.  (This is the only conjunct of `Work.GW2.Case2Pre` that is
*not* a consequence of `Case2Setup9S`'s (1),(2) data plus the three facts `F ≠ ⊥`, `F ≤ C_G(E)`,
`N_G(F) = M` of Bender (3),(4) — those three are proved in a sibling leaf
(`Submission/Work/CORE4/Case2Setup9Fprops.lean`) and are taken here as the last three hypotheses.)

Notation as in Bender §4: `E := layerIn M`, `H = C_G(t) = B.H`, `U = O(H) = B.U`,
`P ≤ M ⊓ H` a Sylow 2-subgroup of `M`, `s ∈ P ⊓ E` an involution with (Bender (1),(2))

* `(invSet (U ⊓ M) s : Set G) = ⁅P ⊓ E, U ⊓ M⁆` (so `K := ⁅P ⊓ E, U ⊓ M⁆ = I_{U⊓M}(s)`) and `K` cyclic;
* `(U ⊓ M) ⊓ C_G(s) = (U ⊓ M) ⊓ C_G(P ⊓ E)`;
* `U ⊓ M = K ⊔ ((U ⊓ M) ⊓ C_G(s))`.

Hypotheses beyond these: `¬ H ≤ M` (Theorem 2.6), `M = E ⊔ (M ⊓ H)` (one class of involutions in
`E`), and §4 (3),(4): `F := ((U ⊓ M) ⊓ C_G(s)) ⊓ F(U) ≠ ⊥`, `F ≤ C_G(E)`, `N_G(F) = M`.

Known reductions (recorded in full in `Submission/Work/NOTES_CORE4.md` and the docstring of the
sibling leaf):
* `C_H(s) = C_U(s)·⟨s,t⟩`, so the goal is `C_H(s) ≤ M`;
* `F = C_{F(U)}(s) ⊓ M` and `F ⊴ M` (from `F ≤ C_G(E)` and `M = E ⊔ (M ⊓ H)`); writing
  `Y := C_{F(U)}(s) ⊇ F`, one has `Yᵘ = Y` and `Fᵘ = Y ⊓ Mᵘ` for every `u ∈ C_U(s)` (`u ∈ U`
  normalises `F(U)`, `sᵘ = s`).  Hence **`C_{F(U)}(s) ⊴ M` suffices**: then `Y ≤ M` (`F ≠ ⊥` is
  not normal in the simple `G` and `Y ≤ U ≤ H < G`), and `C_U(s) ≤ N_G(Y) = N_G(F) = M`;
* equivalently `C_{F(U)}(s) = F` (Bender's printed first half of (5));
* counting does *not* obstruct: `|K|·|U ⊓ M : B₀| = |U ⊓ M|` and `|I_U(s)| = |U : C_U(s)|`
  (Bender 1.5(ii)) give `|I_U(s)| = |K|` whenever `C_U(s) ⊄ M`, which is consistent;
* §4 (6) (`F ⊓ F^g = ⊥` for `g ∉ M`, derivable from Lemma 2.7 = `I.lem27`), applied to
  `u ∈ C_U(s) ∖ M`, gives `F ⊓ Mᵘ = ⊥`;
* Lemma 2.9 (`Work.GW2.Lemma29Prop`, applied to `N := C_G(u)` with `V := ⟨s,t⟩`) is the geometric
  tool Bender uses elsewhere; its hypothesis (`t ∈ O₂(N_G(X))` for `1 ≠ [s',X] = X ≤ U`) is not
  automatically available here.

CORRECTED (design pass 17 item A): `N_G(F) = M` **does** force `F = C_{F(U)}(s)`, exactly as
Bender writes on p. 225 ("`N_G(F) = M`, thus `F = C_{F(U)}(s)`"): normalizers grow in the
nilpotent group `Y = C_{F(U)}(s)`, so `N_Y(F) = Y ⊓ M = F` and
`eq_of_le_isNilpotent_of_normalizer` (below) gives `F = Y`.  The naive closure argument
(`F^m = F(U^m) ⊓ M^m ⊓ C_G(s^m)`) shows only that *that* route fails, not that the statement is
unprovable; the proof is by normalizer growth inside `F(U)`, which is nilpotent. -/
theorem Case2CU_s (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M P : Subgroup G) (s : G),
        IsCoatom M → B.t ∈ Work.GW2.layerIn M → ¬ B.H ≤ M →
        M = Work.GW2.layerIn M ⊔ (M ⊓ B.H) →
        IsPGroup 2 P → P ≤ M ⊓ B.H → ¬ 2 ∣ P.relIndex M →
        s ∈ P ⊓ Work.GW2.layerIn M → orderOf s = 2 →
        (Work.GW2.invSet (B.U ⊓ M) s : Set G) =
            ((⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) : Set G) →
        IsCyclic (⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) →
        ((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) =
            (B.U ⊓ M) ⊓ Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G) →
        B.U ⊓ M = (⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) ⊔
            ((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) →
        (((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ Work.GW2.fittingIn B.U) ≠ ⊥ →
        (((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ Work.GW2.fittingIn B.U) ≤
            Subgroup.centralizer ((Work.GW2.layerIn M : Subgroup G) : Set G) →
        Subgroup.normalizer (((((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓
            Work.GW2.fittingIn B.U) : Subgroup G) : Set G) = M →
        B.U ⊓ Subgroup.centralizer ({s} : Set G) =
            (B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G) := by
  intro G _ _ hbc B M P s hcoat ht hnotH hsup hPg hPle hPidx hsP hs2 hKdef hKcyc hB0eq hKB0
    hFne hFcent hFnorm
  exact Case2CU_s_of_normal I G hbc B M P s hcoat ht hnotH hsup hPg hPle hPidx hsP hs2
    hKdef hKcyc hB0eq hKB0 hFne hFcent hFnorm
    (le_normalizer_CFU_of_normalizer_F B M s hFnorm)

end Work.CORE4
