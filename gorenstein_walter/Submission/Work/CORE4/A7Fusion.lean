import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.M_eq_layerIn_sup_of_oneInvClass

set_option linter.style.haveILetI false

namespace Work.CORE4

open Work.GW2 Subgroup

/-! ## A general group-theory helper

If `E ≤ M` is a normal subgroup of `M` (in the sense `M ≤ N_G(E)`) of **odd** index, then every
element of `M` whose square is `1` (in particular every involution) lies in `E`.

Proof: the canonical projection `M →* M ⧸ (E.subgroupOf M)` sends `u` to an element whose order
divides both `2` and `[M : E]`; the latter is odd, so the image is trivial. -/
theorem mem_of_sq_eq_one_of_odd_relIndex {G : Type} [Group G] [Finite G]
    {E M : Subgroup G} (hEM : E ≤ M) (hME : M ≤ Subgroup.normalizer (E : Set G))
    (hodd : Odd (E.relIndex M)) {u : G} (hu : u ∈ M) (hu2 : u ^ 2 = 1) : u ∈ E := by
  set Q : Subgroup ↥M := E.subgroupOf M with hQ
  haveI hQn : Q.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hEM).mpr hME
  let x : ↥M := ⟨u, hu⟩
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    simpa [x] using hu2
  have hfx2 : (QuotientGroup.mk' Q x) ^ 2 = 1 := by
    rw [← map_pow, hx2, map_one]
  have hdvd2 : orderOf (QuotientGroup.mk' Q x) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hfx2
  have hdvdcard : orderOf (QuotientGroup.mk' Q x) ∣ Nat.card (↥M ⧸ Q) :=
    orderOf_dvd_natCard _
  have hcard : Nat.card (↥M ⧸ Q) = E.relIndex M := by
    rw [← Subgroup.index_eq_card Q, hQ]
    rfl
  have hf1 : QuotientGroup.mk' Q x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      rw [h] at hdvdcard
      rw [hcard] at hdvdcard
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvdcard)
  have hxQ : x ∈ Q := by
    have h1 : x ∈ (QuotientGroup.mk' Q).ker := MonoidHom.mem_ker.mpr hf1
    rwa [QuotientGroup.ker_mk' Q] at h1
  have h2 : (x : G) ∈ E := (Subgroup.mem_subgroupOf (H := E) (K := M)).mp hxQ
  simpa [x] using h2

/-- **`A7Fusion`** (Bender p. 226, the `A₇` case): in the `A₇` configuration every involution
`u ∈ M = C.D.M` is conjugate to `t` by an element of `M`.

Route.  `A7Facts2` gives `S ≤ E := E(M)`; `Case2PrePlus` says the index `[M : S]` is odd (a Sylow
2-subgroup of `M` sits in `E`), and since `S ≤ E ≤ M` the index `[M : E]` is odd too
(`relIndex_mul_relIndex`).  Hence `E`, which is normal in `M`, contains every element of `M` of
order dividing `2` (`mem_of_sq_eq_one_of_odd_relIndex`); in particular `u ∈ E`.  Finally
`Case2Pre`'s `OneInvClassIn (layerIn M)` conjugates `u` to `t` (which lies in `layerIn M`). -/
theorem A7Fusion (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
      Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
        Work.GW2.A7Facts2 B C.D →
          ∀ u : G, orderOf u = 2 → u ∈ C.D.M →
            ∃ m ∈ C.D.M, m * u * m⁻¹ = B.t := by
  intro G _ _ B C hHyp _hA7 _h1 h2 u hu2 huM
  obtain ⟨_hbc, _hc2, hplus, _h7, _h8⟩ := hHyp
  -- `S` lies in `E = layerIn M`, hence in `M`
  have hSE : (B.S : Subgroup G) ≤ Work.GW2.layerIn C.D.M := h2.2.2.1
  have hSM : (B.S : Subgroup G) ≤ C.D.M := le_trans hSE (Work.CORE4.layerIn_le C.D.M)
  -- `E ⊴ M` (as `M ≤ N_G(E)`) and `E ≤ M`
  have hEM : Work.GW2.layerIn C.D.M ≤ C.D.M := Work.CORE4.layerIn_le C.D.M
  have hME : C.D.M ≤ Subgroup.normalizer ((Work.GW2.layerIn C.D.M : Subgroup G) : Set G) :=
    Work.CORE4.layerIn_le_normalizer C.D.M
  -- `[M : S]` is odd (a Sylow 2-subgroup of `M` lies in `E`)
  have hnot2 : ¬ 2 ∣ (B.S : Subgroup G).relIndex C.D.M := by
    have h := hplus.1
    rwa [inf_of_le_left hSM] at h
  -- `[M : S] = [E : S] * [M : E]`, so `[M : E]` is odd
  have hmul : (B.S : Subgroup G).relIndex (Work.GW2.layerIn C.D.M) *
      (Work.GW2.layerIn C.D.M).relIndex C.D.M = (B.S : Subgroup G).relIndex C.D.M :=
    Subgroup.relIndex_mul_relIndex (B.S : Subgroup G) (Work.GW2.layerIn C.D.M) C.D.M hSE hEM
  have hoddE : Odd ((Work.GW2.layerIn C.D.M).relIndex C.D.M) := by
    refine Nat.not_even_iff_odd.mp ?_
    intro hev
    refine hnot2 ?_
    rw [← hmul]
    exact dvd_mul_of_dvd_right (even_iff_two_dvd.mp hev) _
  -- `u ^ 2 = 1`
  have hu2' : u ^ 2 = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu2] at h
    simpa using h
  -- every element of `M` of order dividing `2` lies in `E`
  have huE : u ∈ Work.GW2.layerIn C.D.M :=
    mem_of_sq_eq_one_of_odd_relIndex hEM hME hoddE huM hu2'
  -- one class of involutions in `E`, and `t ∈ E`
  obtain ⟨m, hm, hconj⟩ :=
    C.pre.2.1 u ⟨huE, hu2⟩ B.t ⟨C.D.t_mem, B.t_order⟩
  exact ⟨m, hEM hm, hconj⟩

end Work.CORE4
