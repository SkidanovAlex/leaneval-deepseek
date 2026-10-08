import Mathlib
import Submission.Work.Higman.NSM.dsq_setup
import Submission.Work.Higman.NSM.two_cover_exists
import Submission.Work.Higman.NSM.two_cover_endgame
import Submission.Work.Higman.RedAux.two_cover_stage
import Submission.Work.Higman.NSM.c4sqAMaximal
import Submission.Work.Higman.MSA.centralizer_eq_self
import Submission.Work.Higman.omega1_iso_field
import Submission.Work.Higman.H8.Erad_le_D
import Submission.Work.Higman.H8.false_of_sq_mem_and_comm_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped commutatorElement

namespace Work.Higman.NSM

/-- **The `C₄` exclusion in cover form**, proved by strong induction on `Nat.card P`.

`P` is a Suzuki 2-group, `A` a `ξ`-invariant abelian normal subgroup with `Ω₁(P) ≤ A`,
`[P,P] = A`, every square of `P` in `A`, `A⁴ = 1`, `A² = Ω₁(P)`, `|A| = |Ω₁(P)|²`, and `C` a
minimal `ξ`-invariant normal cover of `A` with `C² = [C,C] = A²` and `[C,⊤] = A`.  Then `False`.

This is the `⁅C,⊤⁆ = A` branch of the `C₄` exclusion.  The minimal-counterexample induction
produces a twin cover `E` (`Work.Higman.NSM.two_cover_exists`: `D ⊓ E = A`, `D ⊔ E = ⊤`,
`⁅D,E⁆ = A`, `D² = E² = A²`, `⁅D,D⁆ = ⁅E,E⁆ = A²`), and the resulting two-cover configuration is
impossible by `Work.Higman.NSM.two_cover_endgame`, which realises the pairings
`β : D/A × E/A → A/A²` and `Φ : A/A² × D/A → A²` over the field `F = Ω₁(P)` with the eigenvalues
`μ, μ, μ²` of `ξ` on `D/A`, `E/A`, `A/A²` and feeds the `c4_resonance_false` endgame (Higman §4
Lemma 6). -/
private theorem c4_cover_false : ∀ m : ℕ, ∀ {Q : Type} [Group Q] [Finite Q], Nat.card Q = m →
    (hQ : Work.Higman.IsSuzuki2Grp Q) →
    ∀ (A C : Subgroup Q),
      Work.Higman.IsXiAbelNormal hQ A → Work.Higman.omega1 Q ≤ A → ⁅(⊤ : Subgroup Q), ⊤⁆ = A →
      (∀ x : Q, x ^ 2 ∈ A) → Work.Higman.powSub A 4 = ⊥ →
      Work.Higman.powSub A 2 = Work.Higman.omega1 Q →
      Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 Q)) ^ 2 →
      C.Normal → C.map (hQ.xi : MulAut Q).toMonoidHom = C → A ≤ C → A ≠ C →
      (∀ D : Subgroup Q, D.Normal → D.map (hQ.xi : MulAut Q).toMonoidHom = D →
        A ≤ D → D ≤ C → D = A ∨ D = C) →
      Work.Higman.powSub C 2 = Work.Higman.powSub A 2 → ⁅C, C⁆ = Work.Higman.powSub A 2 →
      ⁅C, (⊤ : Subgroup Q)⁆ = A → False := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro Q _ _ hcardQ hQ A C hA hNA hGs hsq hA4 htop hcard hCn hCinv hAC hCA hcover hCpow2 hCd hCT
    -- `A` is maximal among the `ξ`-invariant abelian normal subgroups, and `C_P(A) = A`
    have hAxi : A.map (hQ.xi : MulAut Q).toMonoidHom = A := hA.map_eq
    have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
    have hmax : ∀ B : Subgroup Q, Work.Higman.IsXiAbelNormal hQ B → A ≤ B → B = A :=
      Work.Higman.NSM.c4sqAMaximal hQ hAxi hAab hNA hGs hsq hA4 htop hcard
    have hAZ : ¬ A ≤ Subgroup.center Q :=
      Work.Higman.RedAux.c4_A_not_le_center hQ hGs hsq htop hcard
    have hcent : Subgroup.centralizer (A : Set Q) = A :=
      Work.Higman.MSA.centralizer_eq_self hQ hA hmax hNA hGs hsq hA4 htop hcard hAZ
    -- the twin cover, using the induction hypothesis for strictly smaller groups
    obtain ⟨E, hEn, hEinv, hAE, hEA, hEcover, hCE, hCEsup, hEpow2, hEd, hEAd, hCEd⟩ :=
      Work.Higman.NSM.two_cover_exists hQ hA hmax hNA hGs hsq hA4 htop hcard hcent hCn hCinv
        hAC hCA hcover hCpow2 hCd hCT
        (fun {S : Type} [Group S] [Finite S] hS hlt A' C' hA' hNA' hGs' hsq' hA4' htop' hcard'
          hCn' hCinv' hAC' hCA' hcover' hCpow2' hCd' hCT' =>
          ih (Nat.card S) (hcardQ ▸ hlt) rfl hS A' C' hA' hNA' hGs' hsq' hA4' htop' hcard'
            hCn' hCinv' hAC' hCA' hcover' hCpow2' hCd' hCT')
    -- the two-cover configuration is impossible
    have hACd : ⁅A, C⁆ = Work.Higman.powSub A 2 :=
      Work.Higman.RedAux.c4_comm_A_D hQ hA hCinv hA4 hAC hCA hCd htop hcard hcent
    have hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2 := by
      rw [Subgroup.commutator_comm]; exact hACd
    exact Work.Higman.NSM.two_cover_endgame hQ hA hNA hGs hsq hA4 htop hcard hcent hCn hEn
      hCinv hEinv hAC hAE hCA hEA hcover hEcover hCd hEd hCpow2 hEpow2 hCAd hEAd hCE hCEsup

/-- **`deepSquareCase`, the branch `⁅P,D⁆ = A`.**

`P` a Suzuki 2-group, `A, D` satisfying the `C₄` deep configuration
(`Work.Higman.NSM.C4 h A D`), and `⁅P,D⁆ ⊄ A²` (equivalently, since `⁅P,D⁆` is a `ξ`-invariant
subgroup of `A` containing `A² = ⁅D,D⁆`, this says `⁅P,D⁆ = A`; the other branch
`⁅P,D⁆ ≤ A²` is closed by the Gorenstein–Thompson pairing argument and is not part of this
statement).  Then `False`.

Available in this branch: `C_P(A) = A`, `D² = A²`, `|D| = q³`, `P² = A`, the radical of the
commutator pairing `β : P/A × P/A → A/A²` is `0` (`H8.Erad_le_D`), `β` is alternating,
`ξ`-equivariant and onto, and the diagonal identity `⟦x,⟦x,y⟧⟧ = ⟦x,y⟧²` for `x` with `x²`
central (`H8.false_of_sq_mem_and_comm_le`, `RedAux.commutator_diag_eq`).  The proof runs through
the two-cover configuration: `⁅P,D⁆ = A` forces a twin cover `E > A` with `D ⊓ E = A`,
`D ⊔ E = ⊤`, `⟦D,E⟧ = A` and `⟦D,D⟧ = ⟦E,E⟧ = A²` (`Higman/NSM/two_cover_exists`), and the
pairings `β : D/A × E/A → A/A²`, `Φ : A/A² × D/A → A²` together with the eigenvalues
`μ, μ, μ²` of `ξ` on `D/A`, `E/A`, `A/A²` (Frobenius conjugates of the Singer cycle `λ` on
`Ω₁(P)`, with `μ² = λ`) realise Higman §4 Lemma 6 and contradict
`Work.Higman.H8.c4_resonance_false`. -/
theorem dsq_caseB {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A D : Subgroup P} (H : Work.Higman.NSM.C4 h A D)
    (hPD : ¬ (⁅(⊤ : Subgroup P), D⁆ ≤ Work.Higman.powSub A 2)) : False := by
  -- `⁅⊤,D⁆` is a `ξ`-invariant normal subgroup of `A` containing `A² = ⁅D,D⁆`
  have hle : (⁅(⊤ : Subgroup P), D⁆ : Subgroup P) ≤ A := by
    calc ⁅(⊤ : Subgroup P), D⁆ ≤ ⁅(⊤ : Subgroup P), ⊤⁆ := Subgroup.commutator_mono le_rfl le_top
      _ = A := H.Gs
  have hinv : (⁅(⊤ : Subgroup P), D⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom
      = ⁅(⊤ : Subgroup P), D⁆ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective, H.Dinv]
  have hTopD : ⁅(⊤ : Subgroup P), D⁆ = A := by
    rcases Work.Higman.RedAux.red_trichotomy h A ⁅(⊤ : Subgroup P), D⁆ H.isXiAbelNormal H.A4
      hle hinv with hb | hb | hb
    · exfalso
      have h2 : Work.Higman.powSub A 2 = ⊥ := by
        have h1 : (⁅D, D⁆ : Subgroup P) ≤ ⁅(⊤ : Subgroup P), D⁆ :=
          Subgroup.commutator_mono le_top le_rfl
        rw [hb] at h1
        rw [← H.Dd]
        exact le_bot_iff.mp h1
      have h3 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [← H.top, h2]; simp
      have h4 := h.omega1_card_ge_four
      omega
    · exact absurd (le_of_eq hb) hPD
    · exact hb
  have hDtop : ⁅D, (⊤ : Subgroup P)⁆ = A := by
    rw [Subgroup.commutator_comm]; exact hTopD
  exact c4_cover_false (Nat.card P) rfl h A D H.isXiAbelNormal H.NA H.Gs H.sq H.A4 H.top
    H.card H.Dn H.Dinv H.AD (Ne.symm H.ADne) H.cover H.powSub_D_two_eq H.Dd hDtop

end Work.Higman.NSM
