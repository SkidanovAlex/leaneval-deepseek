import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F
import Submission.Work.CORE4.NineRyAux.OddSup
import Submission.Work.CORE4.NineRyAux.InvertsSup
import Submission.Work.CORE4.NineRyAux.SplitH
import Submission.Work.CORE4.NineRyAux.NormFacts

-- the element-commutator notation `⁅g, h⁆`
open scoped commutatorElement

namespace Work.CORE4

open Work.GW2 Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary subgroup lemmas used by `NineRy` -/

/-- `|K^g| = |K|`. -/
theorem card_conjSub_nineRy (g : G) (K : Subgroup G) : Nat.card (conjSub g K) = Nat.card K := by
  rw [conjSub]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- If `y r y⁻¹ = t` and `R` centralizes `r`, then `y R y⁻¹` centralizes `t`. -/
theorem conjSub_le_centralizer_of_conj_eq {y r t : G} {R : Subgroup G}
    (hyr : y * r * y⁻¹ = t) (hRc : R ≤ Subgroup.centralizer ({r} : Set G)) :
    conjSub y R ≤ Subgroup.centralizer ({t} : Set G) := by
  intro g hg
  rw [conjSub, Subgroup.mem_map] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxr : x * r = r * x := Subgroup.mem_centralizer_singleton_iff.mp (hRc hx)
  rw [← hyr]
  calc (y * x * y⁻¹) * (y * r * y⁻¹) = y * (x * r) * y⁻¹ := by group
    _ = y * (r * x) * y⁻¹ := by rw [hxr]
    _ = (y * r * y⁻¹) * (y * x * y⁻¹) := by group

/-- If `y t y⁻¹ = r` and `t` inverts `R`, then `r` inverts `y R y⁻¹`. -/
theorem inverts_conjSub_of_conj_eq {y r t : G} {R : Subgroup G} (hyt : y * t * y⁻¹ = r)
    (hRt : Inverts t R) : Inverts r (conjSub y R) := by
  intro g hg
  rw [conjSub, Subgroup.mem_map] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  have h1 : y⁻¹ * r * y = t := by rw [← hyt]; group
  calc r * (y * x * y⁻¹) * r⁻¹
      = y * (y⁻¹ * r * y) * x * (y⁻¹ * r * y)⁻¹ * y⁻¹ := by group
    _ = y * (t * x * t⁻¹) * y⁻¹ := by rw [h1]; group
    _ = y * x⁻¹ * y⁻¹ := by rw [hRt x hx]
    _ = (y * x * y⁻¹)⁻¹ := by group

/-- `|A ⊔ B| · |A ⊓ B| = |A| · |B|` when `B ≤ N_G(A)` (the cardinality shadow of the second
isomorphism theorem). -/
theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hAB : (A ⊓ B).subgroupOf B = A.subgroupOf B := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  have h1 : (A.subgroupOf B).index * Nat.card ↥(A ⊓ B) = Nat.card ↥B := by
    have hc : Nat.card ↥(A.subgroupOf B) = Nat.card ↥(A ⊓ B) := by
      rw [← hAB]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ B ≤ B)).toEquiv
    rw [← hc]
    exact Subgroup.index_mul_card (A.subgroupOf B)
  have h2 : (A.subgroupOf (A ⊔ B)).index * Nat.card ↥A = Nat.card ↥(A ⊔ B) := by
    have hc : Nat.card ↥(A.subgroupOf (A ⊔ B)) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ B)).toEquiv
    rw [← hc]
    exact Subgroup.index_mul_card (A.subgroupOf (A ⊔ B))
  have hidx : (A.subgroupOf B).index = (A.subgroupOf (A ⊔ B)).index := by
    haveI := Subgroup.normal_subgroupOf_of_le_normalizer h
    haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
    have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B A h
    rw [Subgroup.index_eq_card (A.subgroupOf B),
      Subgroup.index_eq_card (A.subgroupOf (A ⊔ B)), sup_comm]
    exact Nat.card_congr e.toEquiv
  calc Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B)
      = ((A.subgroupOf (A ⊔ B)).index * Nat.card ↥A) * Nat.card ↥(A ⊓ B) := by rw [h2]
    _ = ((A.subgroupOf B).index * Nat.card ↥A) * Nat.card ↥(A ⊓ B) := by rw [hidx]
    _ = Nat.card ↥A * ((A.subgroupOf B).index * Nat.card ↥(A ⊓ B)) := by ring
    _ = Nat.card ↥A * Nat.card ↥B := by rw [h1]

/-- `π(A ⊔ B) ⊆ π(A) ∪ π(B)` when `B` normalizes `A` (so that `A ⊔ B = A · B` and
`|A ⊔ B| · |A ⊓ B| = |A| · |B|`). -/
theorem primesOf_sup_subset_of_le_normalizer {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) :
    Work.GW2.primesOf (A ⊔ B) ⊆ Work.GW2.primesOf A ∪ Work.GW2.primesOf B := by
  have hmul := card_sup_mul_card_inf_of_le_normalizer h
  intro p hp
  rw [Work.GW2.primesOf] at hp ⊢
  obtain ⟨hpp, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
  have h2 : p ∣ Nat.card ↥A * Nat.card ↥B := by
    rw [← hmul]
    exact dvd_mul_of_dvd_left hpdvd _
  rcases hpp.dvd_mul.mp h2 with hA | hB
  · exact Or.inl (Nat.mem_primeFactors.mpr ⟨hpp, hA, Nat.card_pos.ne'⟩)
  · exact Or.inr (Nat.mem_primeFactors.mpr ⟨hpp, hB, Nat.card_pos.ne'⟩)

/-- If `X, N ≤ U` meet trivially, then `|X| ≤ |U : N|`. -/
theorem card_le_relIndex_of_inf_eq_bot {U X N : Subgroup G} (hXU : X ≤ U) (hNU : N ≤ U)
    (hbot : X ⊓ N = ⊥) : Nat.card X ≤ N.relIndex U := by
  let f : ↥X × ↥N → ↥U := fun p => ⟨(p.1 : G) * (p.2 : G), U.mul_mem (hXU p.1.2) (hNU p.2.2)⟩
  have hinj : Function.Injective f := by
    intro p q hpq
    have h : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := by
      have := congrArg (fun z : ↥U => (z : G)) hpq
      simpa [f] using this
    have hmem : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ := by
      have h' := congrArg (fun z => (q.1 : G)⁻¹ * z * (p.2 : G)⁻¹) h
      rw [show (q.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ = (q.1 : G)⁻¹ * (p.1 : G)
            by group,
          show (q.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) * (p.2 : G)⁻¹ = (q.2 : G) * (p.2 : G)⁻¹
            by group] at h'
      exact h'
    have h1 : (q.1 : G)⁻¹ * (p.1 : G) ∈ X ⊓ N := by
      refine Subgroup.mem_inf.mpr ⟨X.mul_mem (X.inv_mem q.1.2) p.1.2, ?_⟩
      rw [hmem]
      exact N.mul_mem q.2.2 (N.inv_mem p.2.2)
    rw [hbot] at h1
    have hx : (q.1 : G)⁻¹ * (p.1 : G) = 1 := Subgroup.mem_bot.mp h1
    have hx12 : (p.1 : G) = (q.1 : G) := by
      have := congrArg (fun z => (q.1 : G) * z) hx
      simpa [mul_assoc] using this
    have hn12 : (p.2 : G) = (q.2 : G) := by
      rw [hx12] at h
      exact mul_left_cancel h
    exact Prod.ext (Subtype.ext hx12) (Subtype.ext hn12)
  have hcard : Nat.card (↥X × ↥N) ≤ Nat.card ↥U := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod] at hcard
  have hrel : N.relIndex U * Nat.card ↥N = Nat.card ↥U := by
    have h := Subgroup.relIndex_mul_card N U
    rwa [inf_eq_left.mpr hNU] at h
  rw [← hrel] at hcard
  exact Nat.le_of_mul_le_mul_right hcard Nat.card_pos

/-! ## The lemma `NineRy` (Bender p. 227, N5d) -/

set_option maxHeartbeats 1000000 in
/-- **LEAF C10.N5d `NineRy`** (Bender p. 227): "`R^y` is a `π'`-subgroup of `U` inverted by `r`.
Lying in `[r,B]KF(U)`, `R^y ∩ BKF(U)` is trivial by (7), and this implies `|R^y| ≤ p` by (8)".

`NineRyProp I` gives, from `Hyp9 G B C`, `NineKData C.D q k k'`, an involution `r ∈ (S ∩ M) ∖ E`,
`R ≤ E ∩ C(r)` of order `k'` inverted by `t`, and `y ∈ C(tr)` with `y r y⁻¹ = t`:
`∃ p, p.Prime ∧ p ∣ Nat.card C.D.K0 ∧ Nat.card R ≤ p`.

Route (design pass 10 §3.3, N5d).  Put `X := conjSub y R`.
* `X ≤ C(y r y⁻¹) = C(t) = H` and `X` is odd, so `X ≤ U` (`H = U S`, `I.toolkit.split`);
* `y t y⁻¹ = r` (using `t` central in `S`), so `r` inverts `X`;
* `π(X) = π(k')` is disjoint from `π = π(K₀) ⊆ π(K) ⊆ π(k)`, and `gcd(k, k') = 1`
  (`|k − k'| = 1`);
* `N := B₀ K F(U)` is a subgroup (`K ⊴ U ∩ M = K B₀`, `F(U) ⊴ U`), `r` normalises `B₀`, `K` and
  `F(U)`, and an element of `N` inverted by `r` lies in `[r, B₀] K F(U)` (`InvertsSup`), a
  `π`-group (Seven conjuncts 2, 4 and 6).  So `X ∩ N = 1`;
* `|X| · |N| = |X N| ≤ |U|`, so `|X| ≤ |U : N|`;
* take `P ≤ F` of prime order `p` (Cauchy, `F ≠ ⊥`); `Case2EightAll` gives `|U : N| ≤ p` and
  `p ∣ |K₀|`. -/
theorem NineRy (I : Work.GW2.C4Inputs) : Work.GW2.NineRyProp I := by
  intro G _ _ B C hH q k k' hkd r hr hr2 hrE R hRE hRc hRk hRt y hy hyr
  obtain ⟨hbc, hc2, hpp, h7, h8⟩ := hH
  obtain ⟨hke, hk'o, hq, hdvd, h3K, hoddK⟩ := hkd
  -- ## 0. Elementary facts about `r`, `t`, `S`
  have hSr : r ∈ (B.S : Subgroup G) := (Subgroup.mem_inf.mp hr).1
  have htt : B.t * B.t = 1 := by
    have h := pow_orderOf_eq_one B.t
    rw [B.t_order, pow_two] at h
    exact h
  have hrr : r * r = 1 := by
    have h := pow_orderOf_eq_one r
    rw [hr2, pow_two] at h
    exact h
  have htr : B.t * r = r * B.t := (BenderSetup.t_central B r hSr).symm
  -- `y` conjugates `r` to `t` and `t` to `r`
  have hyt : y * B.t * y⁻¹ = r := by
    have hcomm : (B.t * r) * y = y * (B.t * r) :=
      (Subgroup.mem_centralizer_iff.mp hy) (B.t * r) (Set.mem_singleton _)
    have h1 : y * (B.t * r) * y⁻¹ = B.t * r := by
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : y * r * y⁻¹ = B.t := hyr
    have h3 : (y * B.t * y⁻¹) * B.t = B.t * r := by
      have h4 : y * (B.t * r) * y⁻¹ = (y * B.t * y⁻¹) * (y * r * y⁻¹) := by group
      rw [h4, h2] at h1
      exact h1
    calc y * B.t * y⁻¹ = (y * B.t * y⁻¹) * (B.t * B.t) := by rw [htt, mul_one]
      _ = ((y * B.t * y⁻¹) * B.t) * B.t := by group
      _ = (B.t * r) * B.t := by rw [h3]
      _ = r := by rw [mul_assoc, ← htr, ← mul_assoc, htt, one_mul]
  -- ## 1. `X := R^y`
  set X : Subgroup G := conjSub y R with hXdef
  have hXcard : Nat.card X = k' := by
    rw [hXdef, card_conjSub_nineRy, hRk]
  have hXodd : Odd (Nat.card X) := by rw [hXcard]; exact hk'o
  have hXH : X ≤ B.H := conjSub_le_centralizer_of_conj_eq hyr hRc
  have hXinv : Inverts r X := by
    rw [hXdef]
    exact inverts_conjSub_of_conj_eq hyt hRt
  -- ## 2. `X ≤ U` (`H = U ⊔ S`, `X` odd)
  have hsplit : B.H = B.U ⊔ (B.S : Subgroup G) :=
    NineRyAux.SplitH I B hbc (layerIn C.D.M) C.D.t_mem r hSr hr2 hrE
  have hXU : X ≤ B.U := by
    refine NineRyAux.OddSup (U := B.U) (S := (B.S : Subgroup G)) (X := X) ?_ ?_ ?_ hXodd
    · rw [← hsplit]; exact BenderSetup.U_normal B
    · exact (B.S).isPGroup'
    · rw [← hsplit]; exact hXH
  -- ## 3. The π-arithmetic (Bender §4 (7))
  have hpiK0 : Work.GW2.primesOf C.D.K0 = B.piFU := h7.2.1
  have hpiK : Work.GW2.primesOf C.D.K ⊆ B.piFU := h7.2.2.2.1
  have hpiComm : Work.GW2.primesOf ⁅(B.S : Subgroup G) ⊓ C.D.M, C.D.B0⁆ ⊆ B.piFU :=
    h7.2.2.2.2.2
  -- `π(K₀) ⊆ π(K) ⊆ {p | p ∣ k}`
  have hK0K : Nat.card C.D.K0 ∣ Nat.card C.D.K :=
    Subgroup.card_dvd_of_le (inf_le_right : C.D.K0 ≤ C.D.K)
  have hpi_dvd_k : ∀ p ∈ B.piFU, p ∣ k := by
    intro p hp
    have h1 : p ∈ Work.GW2.primesOf C.D.K0 := by rw [hpiK0]; exact hp
    exact (Nat.mem_primeFactors.mp h1).2.1 |>.trans (hK0K.trans hdvd)
  -- `k` and `k'` are coprime
  have hcop : Nat.Coprime k k' := by
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hkk : k = k' + 1 := by omega
      rw [hkk, Nat.coprime_self_add_left]
      exact Nat.coprime_one_left k'
    · have hkk : k' = k + 1 := by omega
      rw [hkk, Nat.coprime_self_add_right]
      exact Nat.coprime_one_right k
  -- ## 4. `X ⊓ N = ⊥` for `N := B₀ K F(U)`
  set N : Subgroup G := C.D.B0 ⊔ C.D.K ⊔ Work.GW2.fittingIn B.U with hNdef
  obtain ⟨hrB0, hrK, hrFU, hB0K, hB0FU⟩ := NineRyAux.NormFacts I B C hpp r hr
  have hFUU : Work.GW2.fittingIn B.U ≤ B.U := Subgroup.map_subtype_le _
  -- `K` normalises `F(U)`
  have hNK : C.D.K ≤ Subgroup.normalizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G) := by
    have hiff := (Subgroup.normal_subgroupOf_iff hFUU).mp (fittingIn_subgroupOf_normal B.U)
    rw [Subgroup.le_normalizer_iff]
    intro x hx f hf
    exact hiff f x hf (C.D.K_le_U B hx)
  -- `[B₀, ⟨r⟩] ≤ B₀`
  have hcomm_le_B0 : ⁅C.D.B0, Subgroup.zpowers r⁆ ≤ C.D.B0 := by
    rw [Subgroup.commutator_le]
    intro b hb z hz
    have hzN : z ∈ Subgroup.normalizer (C.D.B0 : Set G) := (Subgroup.zpowers_le.mpr hrB0) hz
    have h1 : z * b⁻¹ * z⁻¹ ∈ C.D.B0 :=
      (Subgroup.mem_normalizer_iff.mp hzN b⁻¹).mp (C.D.B0.inv_mem hb)
    have h2 : ⁅b, z⁆ = b * (z * b⁻¹ * z⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]
    exact C.D.B0.mul_mem hb h1
  have hBN : C.D.B0 ≤ Subgroup.normalizer
      (((C.D.K ⊔ Work.GW2.fittingIn B.U : Subgroup G)) : Set G) :=
    le_trans (le_inf hB0K hB0FU) (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hrN : r ∈ Subgroup.normalizer
      (((C.D.K ⊔ Work.GW2.fittingIn B.U : Subgroup G)) : Set G) :=
    (Subgroup.inf_normalizer_le_normalizer_sup _ _) (Subgroup.mem_inf.mpr ⟨hrK, hrFU⟩)
  have hXN : X ⊓ N = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxX, hxN⟩ := Subgroup.mem_inf.mp hx
    have hxinv : r * x * r⁻¹ = x⁻¹ := hXinv x hxX
    have hxodd : Odd (orderOf x) :=
      Odd.of_dvd_nat hXodd (Subgroup.orderOf_dvd_natCard X hxX)
    have hxN' : x ∈ C.D.B0 ⊔ (C.D.K ⊔ Work.GW2.fittingIn B.U) := by
      rw [hNdef] at hxN
      rwa [sup_assoc] at hxN
    have hxA : x ∈ (C.D.K ⊔ Work.GW2.fittingIn B.U) ⊔
        ⁅C.D.B0, Subgroup.zpowers r⁆ :=
      NineRyAux.InvertsSup hrr hBN hrN hrB0 hxN' hxinv hxodd
    -- every prime of `|K ⊔ F(U)|` lies in `π`
    have hKApi : Work.GW2.primesOf (C.D.K ⊔ Work.GW2.fittingIn B.U) ⊆ B.piFU := by
      have h3 := primesOf_sup_subset_of_le_normalizer
        (A := Work.GW2.fittingIn B.U) (B := C.D.K) hNK
      have heq : C.D.K ⊔ Work.GW2.fittingIn B.U =
          Work.GW2.fittingIn B.U ⊔ C.D.K := sup_comm _ _
      rw [← heq] at h3
      intro p hp
      rcases h3 hp with h4 | h5
      · exact h4
      · exact hpiK h5
    -- every prime of `|[B₀, ⟨r⟩]|` lies in `π`
    have hCommApi : Work.GW2.primesOf ⁅C.D.B0, Subgroup.zpowers r⁆ ⊆ B.piFU := by
      intro p hp
      refine hpiComm (SevenX.PiFU.primesOf_mono ?_ hp)
      refine le_trans (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hr)) ?_
      rw [Subgroup.commutator_comm]
    -- so every element of `A := (K ⊔ F(U)) ⊔ [B₀,⟨r⟩]` has order with prime factors in `π`
    have hxpi : ∀ p, p.Prime → p ∣ orderOf x → p ∈ B.piFU := by
      intro p hp hpdvd
      have hdvdA : p ∣ Nat.card ↥((C.D.K ⊔ Work.GW2.fittingIn B.U) ⊔
          ⁅C.D.B0, Subgroup.zpowers r⁆) :=
        hpdvd.trans (Subgroup.orderOf_dvd_natCard _ hxA)
      have hmem : p ∈ Work.GW2.primesOf ((C.D.K ⊔ Work.GW2.fittingIn B.U) ⊔
          ⁅C.D.B0, Subgroup.zpowers r⁆) :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvdA, Nat.card_pos.ne'⟩
      have h1 := primesOf_sup_subset_of_le_normalizer
        (A := C.D.K ⊔ Work.GW2.fittingIn B.U) (B := ⁅C.D.B0, Subgroup.zpowers r⁆)
        (le_trans hcomm_le_B0 hBN)
      rcases h1 hmem with h2 | h3
      · exact hKApi h2
      · exact hCommApi h3
    have hno : ∀ p, p.Prime → ¬ p ∣ orderOf x := by
      intro p hp hpdvd
      have hpπ : p ∈ B.piFU := hxpi p hp hpdvd
      have hpdvdk : p ∣ k := hpi_dvd_k p hpπ
      have hpdvdk' : p ∣ k' := by
        have h : p ∣ Nat.card X := hpdvd.trans (Subgroup.orderOf_dvd_natCard X hxX)
        rwa [hXcard] at h
      have hp1 : p ∣ Nat.gcd k k' := Nat.dvd_gcd hpdvdk hpdvdk'
      rw [hcop.gcd_eq_one] at hp1
      exact hp.not_dvd_one hp1
    by_contra hxne
    obtain ⟨p, hp, hpdvd⟩ :=
      Nat.exists_prime_and_dvd (fun h => hxne (orderOf_eq_one_iff.mp h))
    exact hno p hp hpdvd
  -- ## 5. `|X| ≤ |U : N|`
  have hB0U : C.D.B0 ≤ B.U := (C.D.B0_le B).trans inf_le_left
  have hKU : C.D.K ≤ B.U := C.D.K_le_U B
  have hNU : N ≤ B.U := by
    rw [hNdef]
    exact sup_le (sup_le hB0U hKU) hFUU
  have hcardX : Nat.card X ≤ N.relIndex B.U := card_le_relIndex_of_inf_eq_bot hXU hNU hXN
  -- ## 6. Cauchy: a subgroup `P ≤ F` of prime order `p`, and Bender §4 (8)
  obtain ⟨p, hp, P, hPF, hPcard⟩ :
      ∃ (p : ℕ), p.Prime ∧ ∃ P : Subgroup G, P ≤ C.D.F ∧ Nat.card P = p := by
    have hFne : C.D.F ≠ ⊥ := Work.GW2.Case2Pre.F_ne B C.D C.pre
    have hcard_ne : Nat.card ↥C.D.F ≠ 1 := fun h => hFne (Subgroup.card_eq_one.mp h)
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard_ne
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥C.D.F) p hpdvd
    refine ⟨p, hp, Subgroup.zpowers (y : G), ?_, ?_⟩
    · rintro z hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact C.D.F.zpow_mem y.2 n
    · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy]
  obtain ⟨A, _hobj, hfacts⟩ := h8 p P hp hPF hPcard
  have hpK0 : p ∣ Nat.card C.D.K0 := hfacts.1
  have hNlep : N.relIndex B.U ≤ p := by
    rw [hNdef]
    exact hfacts.2.2.2.2.2.2.2.2.1
  exact ⟨p, hp, hpK0, by
    rw [show Nat.card R = Nat.card X by rw [hRk, hXcard]]
    exact hcardX.trans hNlep⟩

end Work.CORE4
