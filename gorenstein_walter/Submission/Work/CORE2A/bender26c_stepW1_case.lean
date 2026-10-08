import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.stepEDefs
import Submission.Work.CORE2A.bender26c_key
import Submission.Work.CORE2A.bender26c_stepP1
import Submission.Work.CORE2A.bender26c_stepE
import Submission.Work.CORE2A.pCoreIn_conjSub
import Submission.Work.CORE2A.conj_BenderSetup
import Submission.Work.CORE2A.normalizer_eq_of_coatom
import Submission.Work.ASM.Basic
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.LayerCentralizesFitting
import Submission.Work.BMAX.Bender17i_dedekind_basic

/-!
# CORE2A / `thm26c` — the two decidable cases of Bender's step 3

The remaining gap of Bender 1981, Theorem 2.6, step 3 (`Work.CORE2A.StepW1Prop`, see
`Submission/Work/CORE2A/bender26c_stepE.lean`) is the statement that in the configuration

`P₁ := ⁅⟨t⟩, P ⊓ C_G(s)⁆ ≤ O_p(M^g)`, `P^g ≤ O_p(M^g)`, `M ⊇ N_G(P)`, `s = g t g⁻¹`

*some* maximal subgroup `M'` contains both `N_G(P₁)` and `P^g`.

The natural case split runs on the structure of `F(M^g) ≅ F(M)`:

* **`F(M^g)` Dedekind** (`Work.CORE2A.StepW1CaseDedekindProp`, **proved here**): the witness `P₁`
  gives the relation `M^g ⇝ M'` (with `M'` any coatom containing `N_G(P₁)`), and
  Bender 1970, §1.7(i) in the form “`A ⇝ B` plus `F(A)` Dedekind give `F*(A) ≤ B`”
  (`Work.CORE2A.fstarIn_le_of_BRel_of_fitting_dedekind`, reproved here from
  `Work.BMAX.LayerCentralizesFitting`) forces `F*(M^g) ≤ M'`; then
  `P^g ≤ O_p(M^g) ≤ F(M^g) ≤ F*(M^g)`.
  In particular this covers *both* the case `F*(M^g)` not a prime-power group (where `F(M^g)` is
  Dedekind by `Work.BMAX.fittingIn_dedekind_of_fstarIn_not_pgroup`, currently under repair
  upstream) *and* the case `F(M^g) = O_p(M^g)` abelian, `p` odd.

* **`F(M^g)` not Dedekind** (`Work.CORE2A.StepW1CaseNotDedekindProp`, **open**): by Bender 1970
  §1.6/§1.7 this is the case `F(M^g) = O_p(M^g)` a *non-abelian* `p`-group (`p` odd), i.e. the
  recorded open core of the area — see `Submission/Work/CORE2A/NOTES_CORE2A_thm26c.md`,
  `Submission/Work/BMAX/Defs.lean` and `Submission/Work/BMAX/odd_prime_pcore_abelian.lean`.

Everything proved in this file is unproved-free and rests only on
`propext` / `Quot.sound` / `Classical.choice`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-! ## 0. Elementary helpers for `P₁ = ⁅⟨t⟩, P ⊓ C_G(s)⁆` -/

/-- `P₁ = ⁅⟨t⟩, P ⊓ C_G(s)⁆` lies in `P`. -/
theorem stepP1sub_le {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (P : Subgroup G) (s : G)
    (hHN : B.H ≤ Subgroup.normalizer (P : Set G)) :
    Work.CORE2A.stepP1sub B P s ≤ P := by
  rw [Work.CORE2A.stepP1sub]
  have htN : Subgroup.zpowers B.t ≤ Subgroup.normalizer (P : Set G) :=
    le_trans (Subgroup.zpowers_le.mpr (bSetup_t_mem_H B)) hHN
  exact le_trans (Subgroup.commutator_mono le_rfl inf_le_left)
    (Subgroup.le_normalizer_iff_commutator_le_right.mp htN)

/-- `P₁ ≠ ⊥` as soon as `C_P(s) ≰ C_P(t)` (which is `hbig` of the configuration). -/
theorem stepP1sub_ne_bot {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (P : Subgroup G) (s : G)
    (hbig : ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤
      P ⊓ Subgroup.centralizer ({B.t} : Set G))) :
    Work.CORE2A.stepP1sub B P s ≠ ⊥ := by
  intro hbot
  apply hbig
  have hcom : ⁅Subgroup.zpowers B.t, P ⊓ Subgroup.centralizer ({s} : Set G)⁆ = ⊥ := by
    rw [← Work.CORE2A.stepP1sub]
    exact hbot
  have hle : Subgroup.zpowers B.t ≤
      Subgroup.centralizer ((P ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcom
  have ht := hle (Subgroup.mem_zpowers B.t)
  rw [Subgroup.mem_centralizer_iff] at ht
  refine le_inf inf_le_left ?_
  intro x hx
  have h1 : B.t * x = x * B.t := (ht x hx).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact h1

/-- `N_G(P₁) ≠ ⊤`: `G` is simple, `P₁ ≠ ⊥` and `P₁ ≤ P ≤ M < ⊤`. -/
theorem normalizer_stepP1sub_ne_top (G : Type) [Group G] [Finite G]
    (hctx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (P : Subgroup G) (s : G)
    (hHN : B.H ≤ Subgroup.normalizer (P : Set G))
    (M : Subgroup G) (hM : IsCoatom M) (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (hbig : ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤
      P ⊓ Subgroup.centralizer ({B.t} : Set G))) :
    Subgroup.normalizer ((Work.CORE2A.stepP1sub B P s : Subgroup G) : Set G) ≠ ⊤ := by
  classical
  haveI : IsSimpleGroup G := hctx.simple
  intro hNG
  have hP1leP : Work.CORE2A.stepP1sub B P s ≤ P := stepP1sub_le B P s hHN
  have hP1ne : Work.CORE2A.stepP1sub B P s ≠ ⊥ := stepP1sub_ne_bot B P s hbig
  haveI : (Work.CORE2A.stepP1sub B P s).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact hNG
  rcases Subgroup.Normal.eq_bot_or_eq_top (Work.CORE2A.stepP1sub B P s) with h | h
  · exact hP1ne h
  · have hPM : P ≤ M := fun x hx => hNPM (Subgroup.le_normalizer hx)
    exact hM.ne_top (top_le_iff.mp (h ▸ le_trans hP1leP hPM))

/-- There is a coatom containing `N_G(P₁)`, whenever that normalizer is proper. -/
theorem exists_coatom_ge_normalizer_stepP1sub (G : Type) [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (P : Subgroup G) (s : G)
    (hNG : Subgroup.normalizer ((Work.CORE2A.stepP1sub B P s : Subgroup G) : Set G) ≠ ⊤) :
    ∃ M' : Subgroup G, IsCoatom M' ∧
      Subgroup.normalizer ((Work.CORE2A.stepP1sub B P s : Subgroup G) : Set G) ≤ M' :=
  Work.ASM.exists_coatom_ge_of_ne_top _ hNG

/-! ## 1. The relation `M^g ⇝ M'` with witness `P₁` -/

/-- `P₁ ≤ F(M^g)` in the configuration (Bender 1.10(i) in `M^g`). -/
theorem stepP1sub_le_fitting_conjSub (T : Work.GW2.LocalToolkit)
    (hFT : Work.GW2.FeitThompsonProp)
    (G : Type) [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup G) (hP : IsPGroup p P)
    (hHN : B.H ≤ Subgroup.normalizer (P : Set G))
    (hmin : ∀ Q : Subgroup G, Q < P → IsPGroup p Q →
      B.H ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({B.t} : Set G))
    (hnot : ¬ P ≤ Subgroup.centralizer ({B.t} : Set G))
    (M : Subgroup G) (hM : IsCoatom M) (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (V : Subgroup G) (hV4 : Work.GW2.IsFourGroup V) (hVS : V ≤ (B.S : Subgroup G))
    (htV : B.t ∈ V)
    (g : G) (hgN : g ∈ Subgroup.normalizer (V : Set G)) (hgM : g ∉ M)
    (s : G) (hs : g * B.t * g⁻¹ = s) (hsV : s ∈ V)
    (hbig : ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤
      P ⊓ Subgroup.centralizer ({B.t} : Set G))) :
    Work.CORE2A.stepP1sub B P s ≤ Work.GW2.fittingIn (Work.GW2.conjSub g M) := by
  have h := bender26c_stepP1 T hFT G hctx B p hp hp2 P hP hHN hmin hnot M hM hNPM
    V hV4 hVS htV g hgN hgM s hs.symm hsV hbig
  rw [Work.CORE2A.stepP1sub]
  exact le_trans h (Work.BMAX.pCoreIn_le_fittingIn _ hp)

/-- `M^g ⇝ M'` with witness `P₁`, for any coatom `M' ⊇ N_G(P₁)`. -/
theorem BRel_conjSub_of_coatom_ge (T : Work.GW2.LocalToolkit)
    (hFT : Work.GW2.FeitThompsonProp)
    (G : Type) [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup G) (hP : IsPGroup p P)
    (hHN : B.H ≤ Subgroup.normalizer (P : Set G))
    (hmin : ∀ Q : Subgroup G, Q < P → IsPGroup p Q →
      B.H ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({B.t} : Set G))
    (hnot : ¬ P ≤ Subgroup.centralizer ({B.t} : Set G))
    (M : Subgroup G) (hM : IsCoatom M) (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (V : Subgroup G) (hV4 : Work.GW2.IsFourGroup V) (hVS : V ≤ (B.S : Subgroup G))
    (htV : B.t ∈ V)
    (g : G) (hgN : g ∈ Subgroup.normalizer (V : Set G)) (hgM : g ∉ M)
    (s : G) (hs : g * B.t * g⁻¹ = s) (hsV : s ∈ V)
    (hbig : ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤
      P ⊓ Subgroup.centralizer ({B.t} : Set G)))
    (M' : Subgroup G)
    (hNM' : Subgroup.normalizer ((Work.CORE2A.stepP1sub B P s : Subgroup G) : Set G) ≤ M') :
    Work.GW2.BRel (Work.GW2.conjSub g M) M' :=
  ⟨Work.CORE2A.stepP1sub B P s,
    stepP1sub_le_fitting_conjSub T hFT G hctx B p hp hp2 P hP hHN hmin hnot M hM hNPM
      V hV4 hVS htV g hgN hgM s hs hsV hbig,
    le_trans inf_le_left hNM'⟩

/-- `P^g ≤ F*(M^g)`: in the configuration `P^g ≤ O_p(M^g) ≤ F(M^g) ≤ F*(M^g)`. -/
theorem conjSub_le_fstarIn_conjSub (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    (G : Type) [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup G) (hP : IsPGroup p P)
    (hHN : B.H ≤ Subgroup.normalizer (P : Set G))
    (hmin : ∀ Q : Subgroup G, Q < P → IsPGroup p Q →
      B.H ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({B.t} : Set G))
    (hnot : ¬ P ≤ Subgroup.centralizer ({B.t} : Set G))
    (M : Subgroup G) (hM : IsCoatom M) (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (V : Subgroup G) (hV4 : Work.GW2.IsFourGroup V) (hVS : V ≤ (B.S : Subgroup G))
    (htV : B.t ∈ V)
    (g : G) (hgN : g ∈ Subgroup.normalizer (V : Set G)) (hgM : g ∉ M)
    (s : G) (hs : g * B.t * g⁻¹ = s) (hsV : s ∈ V)
    (hbig : ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤
      P ⊓ Subgroup.centralizer ({B.t} : Set G))) :
    Work.GW2.conjSub g P ≤ Work.GW2.fstarIn (Work.GW2.conjSub g M) :=
  le_trans (conjSub_le_pCoreIn_conj T hFT G hctx B p hp hp2 P hP hHN hmin hnot M hM hNPM
      V hV4 hVS htV g hgN s hs.symm hsV)
    (le_trans (Work.BMAX.pCoreIn_le_fittingIn _ hp) (Work.GW2.fittingIn_le_fstarIn _))

/-! ## 2. Bender 1970, §1.7(i) in the `⇝`-form: `F(A)` Dedekind gives `F*(A) ≤ B` -/

/-- The centraliser of `K` normalises every subgroup of `K`. -/
theorem centralizer_le_normalizer_of_le {G : Type*} [Group G] {K X : Subgroup G}
    (h : X ≤ K) : Subgroup.centralizer (K : Set G) ≤ Subgroup.normalizer (X : Set G) :=
  le_trans (Subgroup.centralizer_le (show (X : Set G) ⊆ (K : Set G) from fun x hx => h hx))
    (Subgroup.centralizer_le_normalizer (X : Set G))

/-- **Bender 1970, §1.7(i)/B81 Lemma 2.3(i), the `Dedekind` step.**  If every subgroup of `F(A)`
is normal in `F(A)` (i.e. `F(A)` is a Dedekind group) then the relation `A ⇝ B` forces
`F*(A) ≤ B`: with the witness `X` of `A ⇝ B` one has `F(A) ≤ N(X)`, while `E(A)` centralises
`F(A) ⊇ X` (`Work.BMAX.LayerCentralizesFitting`) so `E(A) ≤ N(X)` too, and both are contained in
`F*(A)`. -/
theorem fstarIn_le_of_BRel_of_fitting_dedekind {G : Type} [Group G] [Finite G]
    (A B : Subgroup G)
    (hded : ∀ X : Subgroup G, X ≤ Work.GW2.fittingIn A →
      Work.GW2.fittingIn A ≤ Subgroup.normalizer (X : Set G))
    (hrel : Work.GW2.BRel A B) : Work.GW2.fstarIn A ≤ B := by
  obtain ⟨X, hXF, hXB⟩ := hrel
  have hFB : Work.GW2.fittingIn A ≤ B :=
    le_trans (le_inf (hded X hXF) (Work.GW2.fittingIn_le_fstarIn A)) hXB
  have hLN : Work.GW2.layerIn A ≤ Subgroup.normalizer (X : Set G) :=
    le_trans (Work.BMAX.LayerCentralizesFitting G A) (centralizer_le_normalizer_of_le hXF)
  have hLB : Work.GW2.layerIn A ≤ B :=
    le_trans (le_inf hLN (Work.GW2.layerIn_le_fstarIn A)) hXB
  rw [Work.GW2.fstarIn_eq_sup]
  exact sup_le hFB hLB

/-! ## 3. The two cases -/

/-- Configuration of Theorem 2.6, step 3, with the additional case hypothesis that `F(M^g)` is a
Dedekind group (every subgroup of `F(M^g)` is normal in `F(M^g)`). -/
def StepW1CaseDedekindProp : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop) (h23 : Work.GW2.Lemma23Prop)
    (h24 : Work.GW2.Lemma24Prop) (h25 : Work.GW2.Lemma25Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (p : ℕ), p.Prime → p ≠ 2 → ∀ P : Subgroup G,
      IsPGroup p P → B.H ≤ Subgroup.normalizer (P : Set G) →
      (∀ Q : Subgroup G, Q < P → IsPGroup p Q →
        B.H ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({B.t} : Set G)) →
      ¬ P ≤ Subgroup.centralizer ({B.t} : Set G) →
      ∀ (M : Subgroup G), IsCoatom M → Subgroup.normalizer (P : Set G) ≤ M →
      ∀ (V : Subgroup G), Work.GW2.IsFourGroup V → V ≤ (B.S : Subgroup G) → B.t ∈ V →
      ∀ (g : G), g ∈ Subgroup.normalizer (V : Set G) → g ∉ M → ∀ s : G,
        g * B.t * g⁻¹ = s → s ∈ V →
        ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤
          P ⊓ Subgroup.centralizer ({B.t} : Set G)) →
        (∀ X : Subgroup G, X ≤ Work.GW2.fittingIn (Work.GW2.conjSub g M) →
            Work.GW2.fittingIn (Work.GW2.conjSub g M) ≤ Subgroup.normalizer (X : Set G)) →
        ∃ M' : Subgroup G, IsCoatom M' ∧
          Subgroup.normalizer ((Work.CORE2A.stepP1sub B P s : Subgroup G) : Set G) ≤ M' ∧
          Work.GW2.conjSub g P ≤ M'

/-- **Case “`F(M^g)` Dedekind” of Bender's step 3.**  The witness `P₁` gives `M^g ⇝ M'` for any
coatom `M' ⊇ N_G(P₁)`, and `fstarIn_le_of_BRel_of_fitting_dedekind` then forces
`F*(M^g) ≤ M'`, whence `P^g ≤ M'`. -/
theorem stepW1_of_fitting_dedekind : StepW1CaseDedekindProp := by
  intro T h21 h23 h24 h25 G _ _ hFT hctx B p hp hp2 P hP hHN hmin hnot M hM hNPM
    V hV4 hVS htV g hgN hgM s hs hsV hbig hded
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup G := hctx.simple
  obtain ⟨M', hM'coat, hNM'⟩ :=
    exists_coatom_ge_normalizer_stepP1sub G B P s
      (normalizer_stepP1sub_ne_top G hctx B P s hHN M hM hNPM hbig)
  refine ⟨M', hM'coat, hNM', ?_⟩
  have hrel : Work.GW2.BRel (Work.GW2.conjSub g M) M' :=
    BRel_conjSub_of_coatom_ge T hFT G hctx B p hp hp2 P hP hHN hmin hnot M hM hNPM
      V hV4 hVS htV g hgN hgM s hs hsV hbig M' hNM'
  have hF : Work.GW2.fstarIn (Work.GW2.conjSub g M) ≤ M' :=
    fstarIn_le_of_BRel_of_fitting_dedekind _ _ hded hrel
  exact le_trans (conjSub_le_fstarIn_conjSub T hFT G hctx B p hp hp2 P hP hHN hmin hnot M hM
    hNPM V hV4 hVS htV g hgN hgM s hs hsV hbig) hF

/-- Configuration of Theorem 2.6, step 3, with the additional case hypothesis that `F*(M^g)` is
not a prime-power group.  (This case is *discharged* by Bender 1970 §1.6/§1.7 through
`Work.BMAX.fittingIn_dedekind_of_fstarIn_not_pgroup`, which says that then `F(M^g)` — hence by
`StepW1CaseDedekindProp` the whole case — is Dedekind.) -/
def StepW1CaseNotPGroupProp : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop) (h23 : Work.GW2.Lemma23Prop)
    (h24 : Work.GW2.Lemma24Prop) (h25 : Work.GW2.Lemma25Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (p : ℕ), p.Prime → p ≠ 2 → ∀ P : Subgroup G,
      IsPGroup p P → B.H ≤ Subgroup.normalizer (P : Set G) →
      (∀ Q : Subgroup G, Q < P → IsPGroup p Q →
        B.H ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({B.t} : Set G)) →
      ¬ P ≤ Subgroup.centralizer ({B.t} : Set G) →
      ∀ (M : Subgroup G), IsCoatom M → Subgroup.normalizer (P : Set G) ≤ M →
      ∀ (V : Subgroup G), Work.GW2.IsFourGroup V → V ≤ (B.S : Subgroup G) → B.t ∈ V →
      ∀ (g : G), g ∈ Subgroup.normalizer (V : Set G) → g ∉ M → ∀ s : G,
        g * B.t * g⁻¹ = s → s ∈ V →
        ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤
          P ⊓ Subgroup.centralizer ({B.t} : Set G)) →
        (¬ ∃ q : ℕ, q.Prime ∧ IsPGroup q (Work.GW2.fstarIn (Work.GW2.conjSub g M))) →
        ∃ M' : Subgroup G, IsCoatom M' ∧
          Subgroup.normalizer ((Work.CORE2A.stepP1sub B P s : Subgroup G) : Set G) ≤ M' ∧
          Work.GW2.conjSub g P ≤ M'

/-- **Case “`F*(M^g)` not a prime-power group”**, reduced to the Dedekind input
`F*(A)` not a `p`-group ⟹ `F(A)` Dedekind (Bender 1970 §1.6/§1.7,
`Work.BMAX.fittingIn_dedekind_of_fstarIn_not_pgroup`).  The Dedekind provider is taken as an
explicit hypothesis so that this module does not depend on the BMAX module that is currently
being repaired. -/
theorem stepW1_of_fstar_not_isPGroup_of_dedekind
    (hded : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ A : Subgroup G,
      IsCoatom A → (¬ ∃ q : ℕ, q.Prime ∧ IsPGroup q (Work.GW2.fstarIn A)) →
      ∀ X : Subgroup G, X ≤ Work.GW2.fittingIn A →
        Work.GW2.fittingIn A ≤ Subgroup.normalizer (X : Set G)) :
    StepW1CaseNotPGroupProp := by
  intro T h21 h23 h24 h25 G _ _ hFT hctx B p hp hp2 P hP hHN hmin hnot M hM hNPM
    V hV4 hVS htV g hgN hgM s hs hsV hbig hnotp
  classical
  haveI : IsSimpleGroup G := hctx.simple
  have hcoat : IsCoatom (Work.GW2.conjSub g M) := BenderConj.isCoatom_conjSub hM g
  exact stepW1_of_fitting_dedekind T h21 h23 h24 h25 G hFT hctx B p hp hp2 P hP hHN hmin hnot
    M hM hNPM V hV4 hVS htV g hgN hgM s hs hsV hbig
    (hded G hctx.simple (Work.GW2.conjSub g M) hcoat hnotp)

/-- **The open case of Bender's step 3**: `F(M^g)` is *not* Dedekind.  By Bender 1970 §1.6/§1.7
this is exactly the case `F(M^g) = F*(M^g) = O_p(M^g)` a non-abelian `p`-group, `p` odd — the
area's recorded open core (`Submission/Work/BMAX/odd_prime_pcore_abelian.lean`,
`Submission/Work/BMAX/NOTES_dedekind_notPGroup_case.md`). -/
def StepW1CaseNotDedekindProp : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop) (h23 : Work.GW2.Lemma23Prop)
    (h24 : Work.GW2.Lemma24Prop) (h25 : Work.GW2.Lemma25Prop)
    (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (p : ℕ), p.Prime → p ≠ 2 → ∀ P : Subgroup G,
      IsPGroup p P → B.H ≤ Subgroup.normalizer (P : Set G) →
      (∀ Q : Subgroup G, Q < P → IsPGroup p Q →
        B.H ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({B.t} : Set G)) →
      ¬ P ≤ Subgroup.centralizer ({B.t} : Set G) →
      ∀ (M : Subgroup G), IsCoatom M → Subgroup.normalizer (P : Set G) ≤ M →
      ∀ (V : Subgroup G), Work.GW2.IsFourGroup V → V ≤ (B.S : Subgroup G) → B.t ∈ V →
      ∀ (g : G), g ∈ Subgroup.normalizer (V : Set G) → g ∉ M → ∀ s : G,
        g * B.t * g⁻¹ = s → s ∈ V →
        ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤
          P ⊓ Subgroup.centralizer ({B.t} : Set G)) →
        (¬ (∀ X : Subgroup G, X ≤ Work.GW2.fittingIn (Work.GW2.conjSub g M) →
            Work.GW2.fittingIn (Work.GW2.conjSub g M) ≤ Subgroup.normalizer (X : Set G))) →
        ∃ M' : Subgroup G, IsCoatom M' ∧
          Subgroup.normalizer ((Work.CORE2A.stepP1sub B P s : Subgroup G) : Set G) ≤ M' ∧
          Work.GW2.conjSub g P ≤ M'

/-- **`StepW1Prop` from the two cases** (“`F(M^g)` Dedekind” and “`F(M^g)` not Dedekind”). -/
theorem stepW1Prop_of_cases (hDed : StepW1CaseDedekindProp)
    (hNot : StepW1CaseNotDedekindProp) : StepW1Prop := by
  intro T h21 h23 h24 h25 G _ _ hFT hctx B p hp hp2 P hP hHN hmin hnot M hM hNPM
    V hV4 hVS htV g hgN hgM s hs hsV hbig
  classical
  by_cases hded : ∀ X : Subgroup G, X ≤ Work.GW2.fittingIn (Work.GW2.conjSub g M) →
      Work.GW2.fittingIn (Work.GW2.conjSub g M) ≤ Subgroup.normalizer (X : Set G)
  · exact hDed T h21 h23 h24 h25 G hFT hctx B p hp hp2 P hP hHN hmin hnot M hM hNPM
      V hV4 hVS htV g hgN hgM s hs hsV hbig hded
  · exact hNot T h21 h23 h24 h25 G hFT hctx B p hp hp2 P hP hHN hmin hnot M hM hNPM
      V hV4 hVS htV g hgN hgM s hs hsV hbig hded

end Work.CORE2A
