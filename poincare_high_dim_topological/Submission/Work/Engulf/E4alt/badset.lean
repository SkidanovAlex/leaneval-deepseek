import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Api
import Submission.Work.Engulf.E4alt.collisionOfPair
import Submission.Work.Engulf.E4alt.hcolOfClean
import Submission.Work.Engulf.Chain.Sub.Transfer

open Set Metric PL

namespace Work.Engulf.E4alt

theorem badset {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)} {ψ : PL.CubeChart n M}
    {ε : ℝ} (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁) (A : Work.Engulf.Amb n p M V)
    (hq : q + 1 ≤ p + 1)
    {i : ℕ} (hi : i < ND.ord.length)
    (hτcore : f '' PL.simp (ND.ord[i]) ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ))
    (A_τ : PL.E N →ᵃ[ℝ] PL.E n)
    (hτwit : ∀ x ∈ PL.simp (ND.ord[i]), ND.g₁ x = ψ.toFun (A_τ x))
    (hτvv : ∀ v ∈ ND.ord[i], A_τ v = ND.vv v)
    (hτinj : Set.InjOn A_τ (PL.simp (ND.ord[i])))
    (hτhnd : AffineIndependent ℝ (fun v : ↥(ND.ord[i] ∩ ND.Fzv) => ND.vv v))
    (hτcard : (ND.ord[i]).card ≤ n + 1) :
    ∃ J : Set (PL.E n), PL.DomDim J ((q : ℤ) - 2) ∧
      ∀ x ∈ PL.simp (ND.ord[i]),
        ψ.toFun (A_τ x) ∈ ψ.toFun '' PL.closedCube (9 / 16 : ℝ) →
        (ψ.toFun (A_τ x) ∈ X ∨ ∃ y ∈ K ∪ ⋃ j ∈ Finset.range i, ⋃ (hj : j < ND.ord.length),
          ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w), ND.g₁ y = ψ.toFun (A_τ x)) →
        x ∈ PL.simp (ND.ord[i]) ∩ (Work.Engulf.floorOf τ₀ τ₁ ∪
          ⋃ j ∈ Finset.range i, ⋃ (hj : j < ND.ord.length),
            ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w)) ∨ A_τ x ∈ J := by
  classical
  set σ := ND.ord[i] with hσdef
  set Q := (⋃ j ∈ Finset.range i, ⋃ (hj : j < ND.ord.length),
      ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w)) with hQdef
  have hσmem : σ ∈ ND.ord := by rw [hσdef]; exact List.getElem_mem hi
  have hσface : σ ∈ ND.Γ₁.faces := ND.ord_mem σ hσmem
  have hσcard : σ.card = q + 2 := by rw [ND.ord_card σ hσmem, H7.card]
  have hσsubΔ : PL.simp σ ⊆ PL.simp (τ₀ ∪ τ₁) := ND.ord_sub σ hσmem
  have hσVt : ∀ v ∈ σ, v ∈ ND.Vt := fun v hv => (ND.Vt_mem v).mpr ⟨σ, hσface, hv⟩
  -- ## The witness `A_τ` of `g₁` on `simp σ` agrees with the `wit`-witness, so its values
  -- ## lie in the open unit cube.
  obtain ⟨A₀, _hA₀eq, hA₀spec⟩ := ND.wit σ hσface hτcore
  have hAτOpen : ∀ x ∈ PL.simp σ, A_τ x ∈ PL.openCube (1 : ℝ) := by
    intro x hx
    have hAgree : Set.EqOn A_τ A₀ (σ : Set (PL.E N)) := fun v hv => by
      rw [hτvv v hv, (hA₀spec v (Work.Engulf.subset_simp hv)).2 v hv]
    have hxas : x ∈ (affineSpan ℝ (σ : Set (PL.E N)) : Set (PL.E N)) :=
      convexHull_subset_affineSpan (σ : Set (PL.E N)) hx
    rw [AffineMap.eqOn_affineSpan hAgree hxas]
    exact (hA₀spec x hx).1
  have hAτClosed : ∀ x ∈ PL.simp σ, A_τ x ∈ PL.closedCube (1 : ℝ) :=
    fun x hx => Work.Engulf.openCube_subset_closedCube 1 (hAτOpen x hx)
  -- ## Integer bookkeeping: the `DomDim` index of the exceptional sets is `≤ q - 2`.
  have hσcardZ : (σ.card : ℤ) = (q : ℤ) + 2 := by rw [hσcard]; push_cast; ring
  have hkeyX : ∀ T ∈ ND.Xcov, ((σ.card : ℤ) + (T.card : ℤ) - 2 - (n : ℤ)) ≤ (q : ℤ) - 2 := by
    intro T hT
    have h2 : (T.card : ℤ) ≤ (p : ℤ) + 1 := by exact_mod_cast ND.Xcov_card T hT
    have h3 : (p : ℤ) + 3 ≤ (n : ℤ) := by exact_mod_cast A.hp
    omega
  have hkeyLam : ∀ lam : Finset (PL.E N), lam.card ≤ p + 1 →
      ((σ.card : ℤ) + (lam.card : ℤ) - 2 - (n : ℤ)) ≤ (q : ℤ) - 2 := by
    intro lam hlam
    have h2 : (lam.card : ℤ) ≤ (p : ℤ) + 1 := by exact_mod_cast hlam
    have h3 : (p : ℤ) + 3 ≤ (n : ℤ) := by exact_mod_cast A.hp
    omega
  -- ## The `X`-cover part of the exceptional set.
  have hXex : ∀ T (hT : T ∈ ND.Xcov), ∃ D : Set (PL.E n),
      PL.DomDim D ((q : ℤ) - 2) ∧
      A_τ '' PL.simp σ ∩ PL.simp T ⊆ A_τ '' PL.simp (σ ∩ ND.Fzv) ∪ D := by
    intro T hT
    obtain ⟨D, hDdim, hDsub⟩ := ND.fixed σ σ A_τ T hτcard hσVt hτvv hτhnd hT
    exact ⟨D, PL.DomDim.mono_dim (hkeyX T hT) hDdim, hDsub⟩
  let D1 : Finset (PL.E n) → Set (PL.E n) := fun T =>
    if hT : T ∈ ND.Xcov then Classical.choose (hXex T hT) else ∅
  have hD1spec : ∀ T (hT : T ∈ ND.Xcov),
      PL.DomDim (D1 T) ((q : ℤ) - 2) ∧
      A_τ '' PL.simp σ ∩ PL.simp T ⊆ A_τ '' PL.simp (σ ∩ ND.Fzv) ∪ D1 T := by
    intro T hT
    have : D1 T = Classical.choose (hXex T hT) := dif_pos hT
    rw [this]
    exact Classical.choose_spec (hXex T hT)
  -- ## A canonical `wit`-witness on every core face of `Γ₁`, and the pair bound of `NormData`.
  have hwitex : ∀ lam : Finset (PL.E N), lam ∈ ND.Γ₁.faces →
      f '' PL.simp lam ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ) →
      ∃ A_lam : PL.E N →ᵃ[ℝ] PL.E n,
        (∀ x ∈ PL.simp lam, ND.g₁ x = ψ.toFun (A_lam x)) ∧
        (∀ x ∈ PL.simp lam, A_lam x ∈ PL.openCube 1) ∧
        (∀ v ∈ lam, A_lam v = ND.vv v) := by
    intro lam hlam hc
    obtain ⟨A_lam, h1, h2⟩ := ND.wit lam hlam hc
    exact ⟨A_lam, h1, (fun x hx => (h2 x hx).1), (fun v hv => (h2 v (Work.Engulf.subset_simp hv)).2 v hv)⟩
  let A2 : Finset (PL.E N) → (PL.E N →ᵃ[ℝ] PL.E n) := fun lam =>
    if h : (lam ∈ ND.Γ₁.faces ∧ f '' PL.simp lam ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ))
      then Classical.choose (hwitex lam h.1 h.2) else 0
  have hA2spec : ∀ lam (h : lam ∈ ND.Γ₁.faces ∧
        f '' PL.simp lam ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ)),
      (∀ x ∈ PL.simp lam, ND.g₁ x = ψ.toFun (A2 lam x)) ∧
      (∀ x ∈ PL.simp lam, A2 lam x ∈ PL.openCube 1) ∧
      (∀ v ∈ lam, A2 lam v = ND.vv v) := by
    intro lam h
    have : A2 lam = Classical.choose (hwitex lam h.1 h.2) := dif_pos h
    rw [this]
    exact Classical.choose_spec (hwitex lam h.1 h.2)
  have hpairex : ∀ lam : Finset (PL.E N), lam ∈ ND.Γ₁.faces →
      f '' PL.simp lam ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ) →
      PL.simp lam ⊆ K ∪ PL.simp (τ₀ ∪ τ₁) → lam.card ≤ p + 1 →
      ∃ D : Set (PL.E n), PL.DomDim D ((q : ℤ) - 2) ∧
        A_τ '' PL.simp σ ∩ A2 lam '' PL.simp lam ⊆
          A_τ '' PL.simp (σ ∩ lam) ∪
            (A_τ '' PL.simp (σ ∩ ND.Fzv) ∩ A2 lam '' PL.simp (lam ∩ ND.Fzv)) ∪ D := by
    intro lam hlamface hlamcore hlamK hlamcard
    have hlamVt : ∀ v ∈ lam, v ∈ ND.Vt := fun v hv => (ND.Vt_mem v).mpr ⟨lam, hlamface, hv⟩
    have hlamcardN : lam.card ≤ n + 1 := by have := A.hp; omega
    have h2 := hA2spec lam ⟨hlamface, hlamcore⟩
    have hcol := hcolOfClean ND H7 hσface hlamface hτcore hlamcore hσsubΔ hlamK
      A_τ (A2 lam) hτwit h2.1
    obtain ⟨D, hDdim, hDsub⟩ :=
      ND.pair σ lam A_τ (A2 lam) hτcard hlamcardN hσVt hlamVt hτvv h2.2.2 hcol
    exact ⟨D, PL.DomDim.mono_dim (hkeyLam lam hlamcard) hDdim, hDsub⟩
  let P : Finset (PL.E N) → Prop := fun lam =>
    lam ∈ ND.Γ₁.faces ∧
    f '' PL.simp lam ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ) ∧
    PL.simp lam ⊆ K ∪ PL.simp (τ₀ ∪ τ₁) ∧ lam.card ≤ p + 1
  let D2 : Finset (PL.E N) → Set (PL.E n) := fun lam =>
    if h : P lam then Classical.choose (hpairex lam h.1 h.2.1 h.2.2.1 h.2.2.2) else ∅
  have hD2spec : ∀ lam, P lam → PL.DomDim (D2 lam) ((q : ℤ) - 2) ∧
        A_τ '' PL.simp σ ∩ A2 lam '' PL.simp lam ⊆
          A_τ '' PL.simp (σ ∩ lam) ∪
            (A_τ '' PL.simp (σ ∩ ND.Fzv) ∩ A2 lam '' PL.simp (lam ∩ ND.Fzv)) ∪ D2 lam := by
    intro lam hP
    have : D2 lam = Classical.choose (hpairex lam hP.1 hP.2.1 hP.2.2.1 hP.2.2.2) := dif_pos hP
    rw [this]
    exact Classical.choose_spec (hpairex lam hP.1 hP.2.1 hP.2.2.1 hP.2.2.2)
  refine ⟨(⋃ T ∈ ND.Xcov, D1 T) ∪ (⋃ lam ∈ ND.hΓ₁.toFinset.filter P, D2 lam), ?_, ?_⟩
  · refine PL.DomDim.union (PL.DomDim.biUnion (fun T hT => (hD1spec T hT).1)) ?_
    exact PL.DomDim.biUnion (fun lam hlam => (hD2spec lam (Finset.mem_filter.mp hlam).2).1)
  · intro x hx hc9 hbad
    rcases hbad with hX | hcoll
    · -- ## the `X`-case
      have hξcov : A_τ x ∈ ⋃ S ∈ ND.Xcov, PL.simp S :=
        ND.Xcov_cov (A_τ x) (hAτClosed x hx) hX
      rw [PL.mem_iUnion_simp] at hξcov
      obtain ⟨T, hT, hxT⟩ := hξcov
      rcases (hD1spec T hT).2 ⟨⟨x, hx, rfl⟩, hxT⟩ with hfrz | hD
      · exfalso
        obtain ⟨x', hx', hx'eq⟩ := hfrz
        have hx'σ : x' ∈ PL.simp σ := Work.Engulf.simp_mono Finset.inter_subset_left hx'
        have hx'x : x' = x := hτinj hx'σ hx hx'eq
        have hxFzv : x ∈ PL.simp (σ ∩ ND.Fzv) := hx'x ▸ hx'
        have hxL : x ∈ L := ND.Fzv_hull σ hσface hτcore hxFzv
        have hxΔ : x ∈ PL.simp (τ₀ ∪ τ₁) := hσsubΔ hx
        have hfx : f x = ψ.toFun (A_τ x) := by rw [← ND.g₁frz hxL, hτwit x hx]
        exact Set.disjoint_left.mp H7.offX ⟨x, ⟨hxL, hxΔ⟩, hfx⟩ hX
      · exact Or.inr (Or.inl (Set.mem_iUnion₂.mpr ⟨T, hT, hD⟩))
    · -- ## the collision case
      obtain ⟨y, hy, hgy⟩ := hcoll
      obtain ⟨lam, hlamface, hylam, hlameng, hlamK, hlamcard1⟩ : ∃ lam : Finset (PL.E N),
          lam ∈ ND.Γ₁.faces ∧ y ∈ PL.simp lam ∧
          PL.simp lam ⊆ K ∪ Q ∧ PL.simp lam ⊆ K ∪ PL.simp (τ₀ ∪ τ₁) ∧ lam.card ≤ p + 1 := by
        rcases hy with hyK | hyQ
        · obtain ⟨lam, hlam, hylam, hlamK⟩ := (ND.subsp K H7.subK).2 y hyK
          refine ⟨lam, hlam, hylam, ?_, ?_, ?_⟩
          · rw [hQdef]; exact hlamK.trans Set.subset_union_left
          · exact hlamK.trans Set.subset_union_left
          · exact Work.Engulf.Chain.card_le_of_simp_subset_subdivides ND.sub H7.cfg.subH
              (fun t ht htH => H7.cfg.dimH t ht htH) hlam (hlamK.trans Set.subset_union_left)
        · obtain ⟨j, hjmem, h1⟩ := Set.mem_iUnion₂.mp hyQ
          obtain ⟨hjlen, h2⟩ := Set.mem_iUnion.mp h1
          obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp h2
          have hjface : ND.ord[j] ∈ ND.Γ₁.faces := ND.ord_mem _ (List.getElem_mem hjlen)
          have hne : (ND.ord[j].erase w).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hemp
            rw [hemp, Work.Engulf.simp_empty] at hyw
            exact hyw
          have hnew : ND.ord[j].erase w ∈ ND.Γ₁.faces :=
            ND.Γ₁.down_closed hjface (Finset.erase_subset w _) hne
          refine ⟨ND.ord[j].erase w, hnew, hyw, ?_, ?_, ?_⟩
          · intro z hz
            rw [hQdef]
            exact Or.inr (Set.mem_iUnion₂.mpr ⟨j, hjmem,
              Set.mem_iUnion.mpr ⟨hjlen, Set.mem_iUnion₂.mpr ⟨w, hw, hz⟩⟩⟩)
          · intro z hz
            exact Or.inr (ND.ord_sub _ (List.getElem_mem hjlen)
              (Work.Engulf.simp_mono (Finset.erase_subset w _) hz))
          · rw [Finset.card_erase_of_mem hw, ND.ord_card _ (List.getElem_mem hjlen), H7.card]
            omega
      · -- `lam` is core, by mesh fineness
        have hlamcore : f '' PL.simp lam ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ) := by
          rcases ND.mesh lam hlamface with h | h
          · exact h
          · exfalso
            have h9 : ND.g₁ y ∈ ψ.toFun '' PL.closedCube (9 / 16 : ℝ) := by rw [hgy]; exact hc9
            exact h y hylam h9
        have hP : P lam := ⟨hlamface, hlamcore, hlamK, hlamcard1⟩
        have hA2 := hA2spec lam ⟨hlamface, hlamcore⟩
        have heq : A_τ x = A2 lam y := by
          refine Work.Engulf.Alt.CubeChart.eq_of_image_eq ψ (hAτOpen x hx) (hA2.2.1 y hylam) ?_
          rw [← hgy, hA2.1 y hylam]
        have hD2 := hD2spec lam hP
        rcases collisionOfPair ND H7 hi hτcore hlamface hlamcore hlameng A_τ (A2 lam)
            hτwit hA2.1 hτinj (D2 lam) hD2.2 hx hylam heq with hfloor | hD
        · exact Or.inl hfloor
        · refine Or.inr (Or.inr ?_)
          exact Set.mem_iUnion₂.mpr ⟨lam,
            Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset ND.hΓ₁).mpr hlamface, hP⟩, hD⟩

end Work.Engulf.E4alt
