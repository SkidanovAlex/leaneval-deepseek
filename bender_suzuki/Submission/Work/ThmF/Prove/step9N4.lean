import Mathlib
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.step9N4` — Peterfalvi II Ch. V §3, step (9), input **N4**

Let `p = |P|` be a prime, `H ≤ G`, `t ∈ G`, `V = C_D(t)` (`D = H ⊓ H^t`), `W = C_V(K)`, and
`S₁ ≤ V` a non-trivial `p`-subgroup which is a Sylow `p`-subgroup of `N = N_G(S₁)`; put
`T = S₁ ⊓ W`.  Then `N` has a normal subgroup of index `p` containing `T`.

Peterfalvi's argument (§2 Lemma 2 b), p. 250, last paragraph):
* `hL2b` at `X = S₁` gives `N = C_G(S₁) · N_V(S₁)`;
* for `c ∈ C_G(S₁)` and `d ∈ V ∩ N` the commutator `[c·d, y]` (`y ∈ S₁`) equals
  `c [d,y] c⁻¹ = [d,y]` (as `c` centralises `S₁ ∋ [d,y]`), and `[d,y] ∈ [V,V] ≤ W` (`hVW`)
  together with `[d,y] ∈ S₁` gives `[d,y] ∈ T = S₁ ⊓ W`.  Hence `[N,S₁] ≤ T`, i.e. `S₁/T` is
  *central* in `N/T`;
* `T ⊴ N` (the same computation, plus `hWV`: `V` normalises `W`);
* `[N : S₁]` is prime to `p` (`hS₁syl`) and `|S₁ : S₁ ⊓ W| = p` (`hS₁W`), so the image of `S₁`
  in `Q = N/T` is a central Sylow `p`-subgroup of order `p`.  Burnside's normal `p`-complement
  theorem (the transfer map, `MonoidHom.ker_transferSylow_isComplement'`) then produces a normal
  subgroup of `Q` of index `p`, which pulls back to the required `M ⊴ N`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.ThmF.Prove

open Subgroup

/-- A finite group with a **central Sylow `p`-subgroup of order `p`** has a normal subgroup of
index `p`.  Indeed `N_Q(P') ≤ C_Q(P')`, so by Burnside's transfer theorem
(`Subgroup.IsComplement'.index_eq_card` applied to
`MonoidHom.ker_transferSylow_isComplement'`) the kernel of the transfer is a normal subgroup of
index `|P'| = p`. -/
theorem exists_normal_index_eq_prime_of_central_sylow {Q : Type} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (P : Sylow p Q) (hcent : (P : Subgroup Q) ≤ Subgroup.center Q)
    (hcard : Nat.card ↥(P : Subgroup Q) = p) :
    ∃ M : Subgroup Q, M.Normal ∧ M.index = p := by
  have hNP : Subgroup.normalizer (P : Set Q) ≤ Subgroup.centralizer (P : Set Q) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_center_iff.mp (hcent hy) x).symm
  refine ⟨(MonoidHom.transferSylow P hNP).ker, MonoidHom.normal_ker _, ?_⟩
  rw [(Subgroup.isComplement'_comm.mpr
    (MonoidHom.ker_transferSylow_isComplement' P hNP)).index_eq_card]
  exact hcard

/-- A normal subgroup of index `p` in `G ⧸ T` pulls back to a normal subgroup of index `p` in `G`
that contains `T`. -/
theorem exists_normal_index_eq_prime_of_quotient {G : Type} [Group G] [Finite G] {p : ℕ}
    (T : Subgroup G) [T.Normal] (h : ∃ L : Subgroup (G ⧸ T), L.Normal ∧ L.index = p) :
    ∃ M : Subgroup G, M.Normal ∧ M.index = p ∧ T ≤ M := by
  obtain ⟨L, hLnormal, hLindex⟩ := h
  haveI : L.Normal := hLnormal
  refine ⟨L.comap (QuotientGroup.mk' T), Subgroup.normal_comap _, ?_, ?_⟩
  · rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective T)]
    exact hLindex
  · intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : (QuotientGroup.mk' T) x = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hx
    rw [hx1]
    exact L.one_mem

/-- **step (9), input N4** (Peterfalvi II Ch. V §3, p. 250, last paragraph): for a non-trivial
`p`-subgroup `S₁ ≤ V = C_D(t)` (`p = |P|` prime) that is a Sylow `p`-subgroup of `N_G(S₁)` and
satisfies `|S₁ : S₁ ⊓ W| = p`, the normalizer `N_G(S₁)` has a normal subgroup of index `p`
containing `(S₁ ⊓ W)`; the hypotheses `hWV` (`V` normalises `W`), `hVW` (`[V,V] ≤ W`) and `hL2b`
(`N_G(X) = C_G(X)·(V ⊓ N_G(X))` for `1 ≠ X ≤ V`) together give `[N_G(S₁), S₁] ≤ S₁ ⊓ W`, so that
`(S₁ ⊓ W)` is normal in `N_G(S₁)` with `S₁/(S₁ ⊓ W)` central, of order `p`. -/
theorem step9N4 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P S₁ : Subgroup G}
    (hp : (Nat.card P).Prime)
    (hS₁V : S₁ ≤ Submission.Blueprint.centD H t) (hS₁ne : S₁ ≠ ⊥)
    (hS₁p : IsPGroup (Nat.card P) S₁)
    (hS₁syl : ¬ Nat.card P ∣ S₁.relIndex (Subgroup.normalizer (S₁ : Set G)))
    (hS₁W : (S₁ ⊓ Work.ThmF.W H t).relIndex S₁ = Nat.card P)
    (hWV : ∀ a ∈ Submission.Blueprint.centD H t, ∀ b ∈ Work.ThmF.W H t, a * b * a⁻¹ ∈ Work.ThmF.W H t)
    (hVW : ∀ a ∈ Submission.Blueprint.centD H t, ∀ b ∈ Submission.Blueprint.centD H t, a * b * a⁻¹ * b⁻¹ ∈ Work.ThmF.W H t)
    (hL2b : ∀ X : Subgroup G, X ≤ Submission.Blueprint.centD H t → X ≠ ⊥ →
      Subgroup.normalizer (X : Set G) =
        Subgroup.centralizer (X : Set G) ⊔ (Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G))) :
    ∃ M : Subgroup ↥(Subgroup.normalizer (S₁ : Set G)), M.Normal ∧ M.index = Nat.card P ∧
      (S₁ ⊓ Work.ThmF.W H t).subgroupOf (Subgroup.normalizer (S₁ : Set G)) ≤ M := by
  classical
  haveI : Fact (Nat.card P).Prime := ⟨hp⟩
  set N : Subgroup G := Subgroup.normalizer (S₁ : Set G) with hNdef
  set T : Subgroup G := S₁ ⊓ Work.ThmF.W H t with hTdef
  have hS₁N : S₁ ≤ N := by rw [hNdef]; exact Subgroup.le_normalizer
  have hTleS₁ : T ≤ S₁ := by rw [hTdef]; exact inf_le_left
  have hTN : T ≤ N := le_trans hTleS₁ hS₁N
  -- `hL2b` at `X = S₁`: `N = C_G(S₁) · (V ⊓ N)`
  have hNdecomp : N = Subgroup.centralizer (S₁ : Set G) ⊔
      (Submission.Blueprint.centD H t ⊓ N) := by
    rw [hNdef]; exact hL2b S₁ hS₁V hS₁ne
  -- `C_G(S₁)` normalises `T` (it fixes `S₁` pointwise)
  have hCnormT : Subgroup.centralizer (S₁ : Set G) ≤ Subgroup.normalizer (T : Set G) := by
    intro c hc
    have hfix : ∀ z ∈ S₁, c * z * c⁻¹ = z := by
      intro z hz
      have hcomm : z * c = c * z := Subgroup.mem_centralizer_iff.mp hc z hz
      rw [← hcomm]; group
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hfix y (hTleS₁ hy)]; exact hy
    · intro hy
      have hyS : c * y * c⁻¹ ∈ S₁ := hTleS₁ hy
      have h2 : c * (c * y * c⁻¹) * c⁻¹ = c * y * c⁻¹ := hfix _ hyS
      have hyinv : y = c⁻¹ * (c * y * c⁻¹) * c := by group
      have h3 : c⁻¹ * (c * y * c⁻¹) * c = c⁻¹ * (c * (c * y * c⁻¹) * c⁻¹) * c := by rw [h2]
      have h4 : c⁻¹ * (c * (c * y * c⁻¹) * c⁻¹) * c = c * y * c⁻¹ := by group
      rw [hyinv, h3, h4]; exact hy
  -- `V ⊓ N` normalises `T`: `V` normalises `W` (`hWV`) and permutes `S₁` (as `V ⊓ N ≤ N`)
  have hDnormT : Submission.Blueprint.centD H t ⊓ N ≤ Subgroup.normalizer (T : Set G) := by
    have hkey : ∀ g : G, g ∈ Submission.Blueprint.centD H t → g ∈ N → ∀ z : G, z ∈ T →
        g * z * g⁻¹ ∈ T := by
      intro g hgV hgN z hz
      have hzS : z ∈ S₁ := hTleS₁ hz
      have hzW : z ∈ Work.ThmF.W H t := (Subgroup.mem_inf.mp (hTdef ▸ hz)).2
      have hgN' : g ∈ Subgroup.normalizer (S₁ : Set G) := hNdef ▸ hgN
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp hgN' z).mp hzS, hWV g hgV z hzW⟩
    intro d hd
    obtain ⟨hdV, hdN⟩ := Subgroup.mem_inf.mp hd
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => hkey d hdV hdN y hy
    · intro hy
      have h := hkey d⁻¹ ((Submission.Blueprint.centD H t).inv_mem hdV) (N.inv_mem hdN)
        (d * y * d⁻¹) hy
      have heq : d⁻¹ * (d * y * d⁻¹) * (d⁻¹)⁻¹ = y := by group
      rwa [heq] at h
  have hNnormT : N ≤ Subgroup.normalizer (T : Set G) := by
    rw [hNdecomp]; exact sup_le hCnormT hDnormT
  -- hence `T ⊴ N` and `S₁ ⊴ N`
  have hTNnormal : (T.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).mpr hNnormT
  have hS₁Nnormal : (S₁.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS₁N).mpr (by rw [hNdef])
  let TT : Subgroup N := T.subgroupOf N
  let SS : Subgroup N := S₁.subgroupOf N
  haveI hTTnormal : TT.Normal := hTNnormal
  haveI hSSnormal : SS.Normal := hS₁Nnormal
  have hTTleSS : TT ≤ SS := fun x hx => hTleS₁ hx
  let P' : Subgroup (N ⧸ TT) := SS.map (QuotientGroup.mk' TT)
  have hC_le_N : Subgroup.centralizer (S₁ : Set G) ≤ N := by
    rw [hNdef]; exact Subgroup.centralizer_le_normalizer _
  -- the images of `C_G(S₁)` and of `V ⊓ N` in `N ⧸ T` centralise the image of `S₁`
  have hCsub : (Subgroup.centralizer (S₁ : Set G)).subgroupOf N ≤
      Subgroup.comap (QuotientGroup.mk' TT) (Subgroup.centralizer (P' : Set (N ⧸ TT))) := by
    intro x hx
    have hx' : (x : G) ∈ Subgroup.centralizer (S₁ : Set G) := Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hyS₁ : (y : G) ∈ S₁ := Subgroup.mem_subgroupOf.mp hy
    have hcomm : (y : G) * (x : G) = (x : G) * (y : G) :=
      Subgroup.mem_centralizer_iff.mp hx' (y : G) hyS₁
    have hcomm' : y * x = x * y := Subtype.ext hcomm
    rw [← map_mul, ← map_mul, hcomm']
  have hDsub : (Submission.Blueprint.centD H t ⊓ N).subgroupOf N ≤
      Subgroup.comap (QuotientGroup.mk' TT) (Subgroup.centralizer (P' : Set (N ⧸ TT))) := by
    intro x hx
    obtain ⟨hxV, hxN⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hyS₁ : (y : G) ∈ S₁ := Subgroup.mem_subgroupOf.mp hy
    have hyV : (y : G) ∈ Submission.Blueprint.centD H t := hS₁V hyS₁
    -- `[x,y] ∈ S₁ ⊓ W`
    have hker : (QuotientGroup.mk' TT) ((x : N) * y * x⁻¹ * y⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      show ((x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹) ∈ T
      have hxN' : (x : G) ∈ Subgroup.normalizer (S₁ : Set G) := hNdef ▸ hxN
      exact Subgroup.mem_inf.mpr
        ⟨S₁.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN' (y : G)).mp hyS₁) (S₁.inv_mem hyS₁),
          hVW (x : G) hxV (y : G) hyV⟩
    have h1 : (QuotientGroup.mk' TT) x * (QuotientGroup.mk' TT) y * ((QuotientGroup.mk' TT) x)⁻¹ =
        (QuotientGroup.mk' TT) y := by
      refine mul_inv_eq_one.mp ?_
      rw [← hker]
      simp only [map_mul, map_inv]
    calc (QuotientGroup.mk' TT) y * (QuotientGroup.mk' TT) x
        = ((QuotientGroup.mk' TT) x * (QuotientGroup.mk' TT) y * ((QuotientGroup.mk' TT) x)⁻¹)
            * (QuotientGroup.mk' TT) x := by rw [h1]
      _ = (QuotientGroup.mk' TT) x * (QuotientGroup.mk' TT) y := by group
  -- `N ⧸ T` is generated by these two images, hence `P'` is central
  have htop : (⊤ : Subgroup N) = (Subgroup.centralizer (S₁ : Set G)).subgroupOf N ⊔
      (Submission.Blueprint.centD H t ⊓ N).subgroupOf N := by
    rw [← Subgroup.subgroupOf_sup hC_le_N inf_le_right, ← hNdecomp, Subgroup.subgroupOf_self]
  have htop_le : (⊤ : Subgroup (N ⧸ TT)) ≤ Subgroup.centralizer (P' : Set (N ⧸ TT)) := by
    have hmk : (⊤ : Subgroup N).map (QuotientGroup.mk' TT) = ⊤ :=
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective TT)
    rw [← hmk, htop, Subgroup.map_sup]
    exact sup_le (Subgroup.map_le_iff_le_comap.mpr hCsub) (Subgroup.map_le_iff_le_comap.mpr hDsub)
  have hP'center : P' ≤ Subgroup.center (N ⧸ TT) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.mp (htop_le (Subgroup.mem_top g)) z hz).symm
  -- cardinality bookkeeping for the image `P'` of `S₁`
  have hS₁'p : IsPGroup (Nat.card P) SS :=
    IsPGroup.of_equiv hS₁p (Subgroup.subgroupOfEquivOfLe hS₁N).symm
  have hP'p : IsPGroup (Nat.card P) P' :=
    IsPGroup.map hS₁'p (QuotientGroup.mk' TT)
  have hP'index : P'.index = SS.index :=
    Subgroup.index_map_eq SS (QuotientGroup.mk'_surjective TT)
      (by rw [QuotientGroup.ker_mk']; exact hTTleSS)
  have hP'card : Nat.card ↥P' = Nat.card P := by
    have hmul := Subgroup.card_mul_index P'
    rw [hP'index, ← Subgroup.index_eq_card TT] at hmul
    have hSS : SS.index = S₁.relIndex N := rfl
    have hTT : TT.index = T.relIndex N := rfl
    rw [hSS, hTT] at hmul
    have hrel := Subgroup.relIndex_mul_relIndex T S₁ N hTleS₁ hS₁N
    rw [← hrel, hS₁W] at hmul
    have hpos : 0 < S₁.relIndex N :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    exact Nat.mul_right_cancel hpos hmul
  have hP'ndvd : ¬ Nat.card P ∣ P'.index := by
    rw [hP'index]
    exact hS₁syl
  -- Burnside's transfer theorem in `N ⧸ T`, then pull back to `N`
  obtain ⟨M', hM'normal, hM'index⟩ :=
    exists_normal_index_eq_prime_of_central_sylow (hP'p.toSylow hP'ndvd)
      (by rw [IsPGroup.toSylow_coe]; exact hP'center)
      (by rw [IsPGroup.toSylow_coe]; exact hP'card)
  exact exists_normal_index_eq_prime_of_quotient TT ⟨M', hM'normal, hM'index⟩

end Work.ThmF.Prove
