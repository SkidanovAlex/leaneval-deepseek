import Mathlib
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.DoubleTransitivity.Sec5.Defs
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting
import Submission.Work.Fitting.centralizer_pPrimePCore_le
import Submission.Work.Fitting.pCore_le_sylow
import Submission.Work.Fitting.piCore_quotient_eq_bot
import Submission.Work.Fitting.isPSolvable_of_solvable
import Submission.Work.Fitting.isPSolvable_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec6.lemma1` — Bender's lemma (Peterfalvi I, Ch. I §6, Lemma 1)

Let `M` be a finite solvable group, `p` a prime, and `X ≤ M` a subgroup of order prime to `p`
normalised by a Sylow `p`-subgroup `P` of `M`.  Then `X ≤ O_{p'}(M)`.

The proof follows the source: quotient by `K = O_{p'}(M)`, so that `O_{p'}(M/K) = 1`.  The image
`P̄ = PK/K` is a Sylow `p`-subgroup of `M/K` and the image `X̄ = XK/K` is a `p'`-subgroup
normalised by it.  In the quotient, `O_p(M/K)` is contained in every Sylow `p`-subgroup, hence
normalises `X̄`; since `O_p(M/K)` is normal we get `⁅X̄, O_p(M/K)⁆ ≤ X̄ ∩ O_p(M/K) = 1`, i.e.
`X̄ ≤ C(O_p(M/K))`.  By Huppert VI.6.5 in the form available in the library
(`Work.Fitting.centralizer_pCore_le_of_pPrimeCore_eq_bot`), `C(O_p(M/K)) ≤ O_p(M/K)`, so
`X̄ ≤ O_p(M/K)` is simultaneously a `p`-group and a `p'`-group, hence trivial.  Therefore
`X ≤ K = O_{p'}(M)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.DoubleTransitivity.Sec6

theorem lemma1 {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (hMsol : Group.IsSolvable M) {X : Subgroup M} (hX : Nat.Coprime p (Nat.card ↥X))
    {P : Subgroup M} (hP : IsSylowSubgroupOf p P ⊤)
    (hPn : P ≤ Subgroup.normalizer (X : Set M)) :
    X ≤ Submission.Blueprint.pPrimeCore p M := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- replace the blueprint's `O_{p'}` by the Feit–Thompson project's `π`-core
  rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
  let K : Subgroup M := Work.Fitting.pPrimeCore p M
  change X ≤ K
  have hKn : K.Normal := inferInstance
  haveI hpsolM : Work.Fitting.IsPSolvable p M :=
    Work.Fitting.isPSolvable_of_solvable p M
  let π : M →* M ⧸ K := QuotientGroup.mk' K
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective K
  haveI : Finite (M ⧸ K) := Finite.of_surjective π hπsurj
  haveI hpsolQ : Work.Fitting.IsPSolvable p (M ⧸ K) :=
    Work.Fitting.isPSolvable_quotient p M K
  -- `P` is a Sylow `p`-subgroup of `M` in the sense of `Sylow`
  have hPpg : IsPGroup p P := hP.2.1
  have hPidx : ¬ p ∣ P.index := by
    have h := hP.2.2
    rw [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right P] at h
    exact h
  -- its image in the quotient is a `p`-subgroup with index indivisible by `p`
  have hPmapPg : IsPGroup p (P.map π) := hPpg.map π
  have hPmapIdx : ¬ p ∣ (P.map π).index := by
    intro h
    exact hPidx (h.trans (Subgroup.index_map_dvd (H := P) hπsurj))
  -- `O_p(M ⧸ K)` is contained in every Sylow, in particular in the image of `P`
  have hQleSmap : Work.Fitting.pCore p (M ⧸ K) ≤ P.map π :=
    Work.Fitting.pCore_le_sylow (hPmapPg.toSylow hPmapIdx)
  -- `P̄` normalises `X̄`, hence so does `O_p(M ⧸ K)`
  have hcomm : ⁅X, P⁆ ≤ X :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := P) (K := X)).mp hPn
  have hcommM : ⁅X.map π, P.map π⁆ ≤ X.map π := by
    rw [← Subgroup.map_commutator (H₁ := X) (H₂ := P) (f := π)]
    exact Subgroup.map_mono hcomm
  have hSmap_le_norm : P.map π ≤
      Subgroup.normalizer ((X.map π : Subgroup (M ⧸ K)) : Set (M ⧸ K)) :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := P.map π) (K := X.map π)).mpr hcommM
  have hQ_le_norm : Work.Fitting.pCore p (M ⧸ K) ≤
      Subgroup.normalizer ((X.map π : Subgroup (M ⧸ K)) : Set (M ⧸ K)) :=
    hQleSmap.trans hSmap_le_norm
  have hcomm_le_Xb : ⁅X.map π, Work.Fitting.pCore p (M ⧸ K)⁆ ≤ X.map π :=
    (Subgroup.le_normalizer_iff_commutator_le_left
      (H := Work.Fitting.pCore p (M ⧸ K)) (K := X.map π)).mp hQ_le_norm
  have hcomm_le_Q : ⁅X.map π, Work.Fitting.pCore p (M ⧸ K)⁆ ≤
      Work.Fitting.pCore p (M ⧸ K) :=
    Subgroup.commutator_le_right (X.map π) (Work.Fitting.pCore p (M ⧸ K))
  -- `X̄ ⊓ O_p(M ⧸ K) = ⊥` because `|X̄|` is prime to `p` while `O_p` is a `p`-group
  have hXb_cop : Nat.Coprime (Nat.card ↥(X.map π)) p :=
    (hX.coprime_dvd_right (Subgroup.card_map_dvd X π)).symm
  have hcop : Nat.Coprime (Nat.card ↥(X.map π))
      (Nat.card ↥(Work.Fitting.pCore p (M ⧸ K))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      (Work.Fitting.isPGroup_pCore (G := M ⧸ K) hp)
    rw [hk]
    exact Nat.Coprime.pow_right k hXb_cop
  have hdisj : X.map π ⊓ Work.Fitting.pCore p (M ⧸ K) = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  have hcomm_bot : ⁅X.map π, Work.Fitting.pCore p (M ⧸ K)⁆ = ⊥ :=
    le_bot_iff.mp ((le_inf hcomm_le_Xb hcomm_le_Q).trans (le_of_eq hdisj))
  have hXb_le_cent : X.map π ≤ Subgroup.centralizer
      ((Work.Fitting.pCore p (M ⧸ K) : Subgroup (M ⧸ K)) : Set (M ⧸ K)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot
  -- `C(O_p) ≤ O_p` in a `p`-solvable group with trivial `O_{p'}`
  have hcore : Work.Fitting.pPrimeCore p (M ⧸ K) = ⊥ :=
    Work.Fitting.piCore_quotient_eq_bot (fun q => q ≠ p) M
  have hXb_le_Q : X.map π ≤ Work.Fitting.pCore p (M ⧸ K) :=
    hXb_le_cent.trans
      (Work.Fitting.centralizer_pCore_le_of_pPrimeCore_eq_bot p (M ⧸ K) hp hcore)
  -- `X̄` is at once a `p`-group and a `p'`-group, hence trivial
  have hXb_bot : X.map π = ⊥ := by
    have hle : X.map π ≤ ⊥ := by
      rw [← hdisj]
      exact le_inf le_rfl hXb_le_Q
    exact le_bot_iff.mp hle
  -- consequently `X ≤ K = O_{p'}(M)`
  have hXK : X ≤ K := by
    have h : X ≤ π.ker := (Subgroup.map_eq_bot_iff X (f := π)).mp hXb_bot
    rwa [QuotientGroup.ker_mk'] at h
  exact hXK

end Work.DoubleTransitivity.Sec6
