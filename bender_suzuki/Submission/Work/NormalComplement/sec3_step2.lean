/-
# Peterfalvi I Ch. III §3 Prop. 1, step 2 (p.177)

**Every prime `p` dividing `|E : E'|` divides `|F(E ∩ V)|`**, where `E = Egrp H t W = W ⊓ D`,
`E' = Ecomm H t W`, `V = centD H t`.

Source argument: let `P` be a subgroup of order `p` of `E ∩ V` (it exists by (D1)), put
`Q = F(E ∩ V)`, and suppose `p ∤ |Q|`.  Since `C_K(P) = 1` by (D1), Appendix VII gives
`K = C_K([P,Q])`, so `[P,Q] ⊆ C_V(K) = 1`.  Hence `P` centralises `F(E ∩ V)`, so `P ⊆ Q` by
Fitting's theorem (`C(F) ⊆ F` in the solvable group `E ∩ V`), contradiction.

The coprimality `(|K|, |QP|) = 1` needed by Appendix VII splits in two: `p ∤ |K|` because the
`p`-group `P` acts fixed-point-freely on `K` (`orbit_conj_unique_fixed`), and `q ∤ |K|` for a
prime `q ∣ |Q|` because `Q ≤ F(V)` (Fitting is monotone in a normal subgroup,
`fitSub_le_fitSub_of_normal`) and `NoCentralizedNormal` yields a nontrivial `V`-normal
`q`-subgroup of `V` (`normal_pSubgroup_of_dvd_fitting`) on which the same orbit count applies.
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Sec3Aux
import Submission.Work.NormalComplement.normal_pSubgroup_of_dvd_fitting
import Submission.Work.NormalComplement.card_sup_mul_card_inf
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.fitting_eq_iSup_pCore
import Submission.Work.Fitting.centralizer_fitting_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

theorem sec3_step2 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hVII : Work.NormalComplement.Design.AppVIIProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G}
    (h : Work.NormalComplement.Design.Setup3 G H t W)
    (hN : Work.NormalComplement.Design.NoCentralizedNormal H t)
    (hK : ∃ K : Subgroup G,
      (K : Set G) = Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t ∧
      Work.NormalComplement.IsNormalComplementOf K (Submission.Blueprint.centD H t)
        (Submission.Blueprint.twoPoint H t))
    (hCV : Submission.Blueprint.centD H t ⊓
      Subgroup.centralizer (Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t :
        Set G) = ⊥) :
    ∀ p : ℕ, p.Prime →
      p ∣ (Work.NormalComplement.Design.Ecomm H t W).relIndex
            (Work.NormalComplement.Design.Egrp H t W) →
      p ∣ Nat.card ↥(Work.NormalComplement.Design.fitSub
            (Work.NormalComplement.Design.Egrp H t W ⊓ Submission.Blueprint.centD H t)) := by
  classical
  intro p hp hdvd
  -- notation: `T = E ⊓ V` and `Q = F(T)`
  set T : Subgroup G :=
    Work.NormalComplement.Design.Egrp H t W ⊓ Submission.Blueprint.centD H t with hT
  set Q : Subgroup G := Work.NormalComplement.Design.fitSub T with hQ
  by_contra hnotQ
  -- the normal complement datum `D = K ⋊ V`
  obtain ⟨K, hKset, hKnc⟩ := hK
  have hKD : K ≤ Submission.Blueprint.twoPoint H t := hKnc.1
  have hKN : Submission.Blueprint.twoPoint H t ≤ Subgroup.normalizer (K : Set G) := hKnc.2.1
  have hVleD : Submission.Blueprint.centD H t ≤ Submission.Blueprint.twoPoint H t := inf_le_left
  have hVNK : Submission.Blueprint.centD H t ≤ Subgroup.normalizer (K : Set G) :=
    hVleD.trans hKN
  have hoddD : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := h.se.2.2 t h.notMem
  -- `T ≤ V` and `V ≤ N_G(T)`, i.e. `T ⊴ V`
  have hTV : T ≤ Submission.Blueprint.centD H t := by
    rw [hT]; exact inf_le_right
  have hNV : Submission.Blueprint.centD H t ≤ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro v hv x hx
    rw [hT] at hx
    obtain ⟨hxE, hxV⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxW, hxD⟩ := Subgroup.mem_inf.mp hxE
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (h.normal ((inf_le_left : Submission.Blueprint.twoPoint H t ≤ H) (hVleD hv))) x).mp hxW
    · exact (Submission.Blueprint.twoPoint H t).mul_mem
        ((Submission.Blueprint.twoPoint H t).mul_mem (hVleD hv) hxD)
        ((Submission.Blueprint.twoPoint H t).inv_mem (hVleD hv))
    · exact (Submission.Blueprint.centD H t).mul_mem
        ((Submission.Blueprint.centD H t).mul_mem hv hxV)
        ((Submission.Blueprint.centD H t).inv_mem hv)
  -- `Q ≤ F(V)`
  have hQFV : Q ≤ Submission.Blueprint.centD H t := by
    rw [hQ]; exact (fitSub_le T).trans hTV
  have hQleFV : Q ≤ Work.NormalComplement.Design.fitSub (Submission.Blueprint.centD H t) := by
    rw [hQ]; exact fitSub_le_fitSub_of_normal hTV hNV
  haveI : Fact p.Prime := ⟨hp⟩
  -- (D1): a subgroup of order `p` of `E ⊓ V` acting fixed-point-freely on `K`
  obtain ⟨P, hPsyl, hPV, hPfpf, -⟩ := h.d1 p hp hdvd
  have hPE : P ≤ Work.NormalComplement.Design.Egrp H t W := hPsyl.2.1
  have hdvdE : p ∣ Nat.card ↥(Work.NormalComplement.Design.Egrp H t W) :=
    hdvd.trans (Subgroup.relIndex_dvd_card _ _)
  have hpP : p ∣ Nat.card ↥P := by
    have h1 : Nat.card ↥P * (P.subgroupOf (Work.NormalComplement.Design.Egrp H t W)).index =
        Nat.card ↥(Work.NormalComplement.Design.Egrp H t W) := by
      have h2 := Subgroup.card_mul_index (P.subgroupOf (Work.NormalComplement.Design.Egrp H t W))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPE).toEquiv] at h2
    rw [← h1] at hdvdE
    exact (hp.dvd_mul.mp hdvdE).resolve_right hPsyl.2.2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpP
  set P₀ : Subgroup G := (Subgroup.zpowers x).map P.subtype with hP₀
  have hP₀card : Nat.card P₀ = p := by
    rw [hP₀, Subgroup.card_map_of_injective (Subgroup.subtype_injective P), Nat.card_zpowers, hx]
  have hP₀leP : P₀ ≤ P := by rw [hP₀]; exact Subgroup.map_subtype_le _
  have hP₀ne : P₀ ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot P₀).mp (by rw [hP₀card]; exact hp.one_lt)
  have hP₀T : P₀ ≤ T := by
    rw [hP₀, hT]
    exact (Subgroup.map_subtype_le _).trans (le_inf hPE hPV)
  have hP₀KV : P₀ ≤ Submission.Blueprint.centD H t := hP₀T.trans hTV
  have hP₀NK : P₀ ≤ Subgroup.normalizer (K : Set G) := hP₀KV.trans hVNK
  have hP₀NQ : P₀ ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQ]; exact hP₀T.trans (fitSub_le_normalizer T)
  have hP₀prime : (Nat.card P₀).Prime := by rw [hP₀card]; exact hp
  have hP₀pg : IsPGroup p ↥P₀ := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [hP₀card, pow_one]⟩
  have hex : ∃ y ∈ P₀, y ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one P₀ with hbot | h
    · exact absurd hbot hP₀ne
    · exact h
  -- `p ∤ |K|`, since `P₀` acts fixed-point-freely on `Kset = K`
  have hpK : ¬ p ∣ Nat.card K :=
    not_dvd_card_of_fpf_pgroup hp hP₀NK hP₀pg (fun a ha hfix => by
      obtain ⟨y, hy, hyne⟩ := hex
      have haKset : a ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t := by
        rw [← hKset]; exact ha
      exact hPfpf y (hP₀leP hy) hyne a haKset (hfix y hy))
  have hcop_p : Nat.Coprime (Nat.card K) p := (hp.coprime_iff_not_dvd.mpr hpK).symm
  -- `q ∤ |K|` for every prime `q ∣ |Q|`
  have hnot_prime : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥Q → ¬ q ∣ Nat.card K := by
    intro q hq hqQ
    have hqFV : q ∣ Nat.card ↥(Work.NormalComplement.Design.fitSub
        (Submission.Blueprint.centD H t)) := hqQ.trans (Subgroup.card_dvd_of_le hQleFV)
    obtain ⟨X, hXV, hVNX, hXpg, hXne⟩ :=
      normal_pSubgroup_of_dvd_fitting (V := Submission.Blueprint.centD H t) hq hqFV
    have hCKX : Work.NormalComplement.Design.CK H t X = {1} := hN X hXne hXV hVNX
    exact not_dvd_card_of_fpf_pgroup hq (hXV.trans hVNK) hXpg (fun a ha hfix => by
      have haKset : a ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t := by
        rw [← hKset]; exact ha
      have haC : a ∈ Subgroup.centralizer (X : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h1 : y * a * y⁻¹ = a := hfix y hy
        calc y * a = y * a * y⁻¹ * y := by group
          _ = a * y := by rw [h1]
      have hmem : a ∈ Work.NormalComplement.Design.CK H t X := ⟨haKset, haC⟩
      rw [hCKX] at hmem
      exact Set.mem_singleton_iff.mp hmem)
  have hcop_Q : Nat.Coprime (Nat.card K) (Nat.card ↥Q) :=
    Nat.coprime_of_dvd' fun q hq hqK hqQ => absurd hqK (hnot_prime q hq hqQ)
  -- the coprime hypothesis of Appendix VII
  have hcop_sup : Nat.Coprime (Nat.card K) (Nat.card ↥(Q ⊔ P₀)) := by
    have hmul : Nat.Coprime (Nat.card K) (Nat.card ↥Q * Nat.card ↥P₀) :=
      hcop_Q.mul_right (by rw [hP₀card]; exact hcop_p)
    have hdvd_sup : Nat.card ↥(Q ⊔ P₀) ∣ Nat.card ↥Q * Nat.card ↥P₀ :=
      ⟨Nat.card ↥(Q ⊓ P₀), (Work.NormalComplement.card_sup_mul_card_inf hP₀NQ).symm⟩
    exact hmul.coprime_dvd_right hdvd_sup
  have hoddQ : Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P₀ : Set G))) := by
    refine Odd.of_dvd_nat hoddD (Subgroup.card_dvd_of_le ?_)
    rw [hQ]
    exact le_trans inf_le_left ((fitSub_le T).trans (hTV.trans hVleD))
  have hKC : K ⊓ Subgroup.centralizer (P₀ : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    obtain ⟨hkK, hkC⟩ := Subgroup.mem_inf.mp hk
    obtain ⟨y, hy, hyne⟩ := hex
    have hfix : y * k * y⁻¹ = k := by
      have h1 := (Subgroup.mem_centralizer_iff.mp hkC) y hy
      rw [h1]; group
    exact hPfpf y (hP₀leP hy) hyne k (by rw [← hKset]; exact hkK) hfix
  have hQNK : Q ≤ Subgroup.normalizer (K : Set G) := hQFV.trans hVNK
  -- Appendix VII
  have hcomm : ⁅P₀, Q⁆ ≤ Subgroup.centralizer (K : Set G) :=
    hVII hFT G K Q P₀ hQNK hP₀NK hP₀NQ hP₀prime (by rw [hP₀card]; exact hnotQ)
      hoddQ hcop_sup hKC
  -- `[P₀,Q] ≤ V ⊓ C_G(K) = 1`
  have hcommV : ⁅P₀, Q⁆ ≤ Submission.Blueprint.centD H t :=
    (Subgroup.commutator_le_sup P₀ Q).trans (sup_le (hP₀T.trans hTV) hQFV)
  have hcommC : ⁅P₀, Q⁆ ≤ Subgroup.centralizer
      (Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t : Set G) := by
    have h1 := hcomm
    rw [hKset] at h1
    exact h1
  have hcommBot : ⁅P₀, Q⁆ = ⊥ := le_bot_iff.mp (hCV ▸ le_inf hcommV hcommC)
  -- Fitting's theorem in the solvable group `T`: `P₀ ≤ C_T(F(T)) ≤ F(T) = Q`
  have hcommCQ : P₀ ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
  have hTodd : Odd (Nat.card ↥T) :=
    Odd.of_dvd_nat hoddD (Subgroup.card_dvd_of_le (hTV.trans hVleD))
  haveI hsolvT : Group.IsSolvable ↥T := hFT ↥T hTodd
  have hkey : P₀.subgroupOf T ≤ Work.Fitting.fitting ↥T := by
    refine le_trans ?_ (Work.Fitting.centralizer_fitting_le ↥T)
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    apply Subtype.ext
    have hzP : (z : G) ∈ P₀ := hz
    have hfQ : (f : G) ∈ Q := by rw [hQ]; exact ⟨f, hf, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hcommCQ hzP)) (f : G) hfQ
  have hP₀Q : P₀ ≤ Q := by
    have h1 : (P₀.subgroupOf T).map T.subtype ≤ Q := by
      rw [hQ]; exact Subgroup.map_mono (f := T.subtype) hkey
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP₀T] at h1
  -- contradiction
  have hpQ : p ∣ Nat.card ↥Q := by
    rw [← hP₀card]
    exact Subgroup.card_dvd_of_le hP₀Q
  exact hnotQ hpQ

end Work.NormalComplement
