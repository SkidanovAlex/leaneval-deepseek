import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.LocalCFT.Units

/-- **The quotient of a finite-index subgroup by its `ℓ`-th powers is no larger than the
quotient of the ambient group by its `ℓ`-th powers.**

Write `P = G ^ ℓ ≤ G` for the range of the `ℓ`-th power map on `G` and, for a subgroup
`V ≤ G` of finite index, `W = (V ^ ℓ)` for the range of the `ℓ`-th power map on `V`
(viewed inside `G`).  Then `W ≤ V ⊓ P ≤ V, P`, and the two index factorisations

* `[V : W] = [V : V ⊓ P] * [(V ⊓ P) : W]` (multiplicativity of the index in the tower
  `W ≤ V ⊓ P ≤ V`), and
* `[G : P] = [G : V ⊔ P] * [(V ⊔ P) : P] = [G : V ⊔ P] * [V : V ⊓ P]`
  (multiplicativity of the index in `P ≤ V ⊔ P ≤ G`, plus the second isomorphism theorem)

reduce the claim to `[(V ⊓ P) : W] ≤ [G : V ⊔ P]`, i.e. to
`|(V ⊓ P)/W| ≤ |G/(V · P)|`.

The latter is the homological input: the `ℓ`-power exact sequences for `G/V` and the snake
lemma give an injection `(V ⊓ P)/W ↪ (G/V)[ℓ]` (this is where the `ℓ`-th powers of `V`
inside `V ⊓ P` are matched with the `ℓ`-torsion of `G/V`), while
`(G/V)[ℓ] ≅ (G/V)/(G/V)^ℓ` has the cardinality of `G/(V · P)` since `V` has finite index
(so that `G/V` is finite).  In this file the injection is realised as the explicit
surjection

  `(V ⊔ P)^ℓ ↶ (preimage of V under the ℓ-th power map) / V ≅ (G/V)[ℓ]`

onto `(V ⊓ P)/W`. -/
theorem natCard_quot_powSubgroup_le {G : Type*} [CommGroup G] (V : Subgroup G)
    (hV : V.FiniteIndex) (ℓ : ℕ) :
    Nat.card (↥V ⧸ (powMonoidHom ℓ : ↥V →* ↥V).range) ≤
      Nat.card (G ⧸ (powMonoidHom ℓ : G →* G).range) := by
  classical
  -- abbreviations
  set P : Subgroup G := (powMonoidHom ℓ : G →* G).range with hP
  set W' : Subgroup ↥V := (powMonoidHom ℓ : ↥V →* ↥V).range with hW'
  set W : Subgroup G := W'.map V.subtype with hW
  set D : Subgroup G := V ⊓ P with hD
  set S : Subgroup G := Subgroup.comap (powMonoidHom ℓ : G →* G) V with hS
  let Q := G ⧸ V
  set Qpow : Subgroup Q := (powMonoidHom ℓ : Q →* Q).range with hQpow
  set Qtors : Subgroup Q := (powMonoidHom ℓ : Q →* Q).ker with hQtors
  -- basic containments
  have hWleV : W ≤ V := by rw [hW]; exact Subgroup.map_subtype_le W'
  have hWleP : W ≤ P := by
    intro x hx
    rw [hW, Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hW', MonoidHom.mem_range] at hy
    obtain ⟨z, rfl⟩ := hy
    rw [hP, MonoidHom.mem_range]
    refine ⟨V.subtype z, ?_⟩
    show (V.subtype z) ^ ℓ = V.subtype ((powMonoidHom ℓ : ↥V →* ↥V) z)
    rw [← map_pow V.subtype z ℓ]
    rfl
  have hWD : W ≤ D := fun x hx => ⟨hWleV hx, hWleP hx⟩
  have hDV : D ≤ V := fun x hx => hx.1
  -- `W.subgroupOf V` is the range of the power map on `V`
  have hWsub : W.subgroupOf V = W' := Subgroup.ext fun x => by
    rw [Subgroup.mem_subgroupOf, hW, Subgroup.mem_map, hW']
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = x := Subtype.ext hxy
      rwa [← hyx]
    · intro hx
      exact ⟨x, hx, rfl⟩
  -- index factorisation inside `V`
  have hC : Nat.card (↥V ⧸ W') = W.relIndex D * D.relIndex V := by
    rw [← hWsub]
    exact (Subgroup.relIndex_mul_relIndex W D V hWD hDV).symm
  -- index factorisation inside `G`
  have hDrel : P.relIndex (V ⊔ P) = D.relIndex V := by
    rw [Subgroup.relIndex_sup_right V P, ← Subgroup.inf_relIndex_right P V]
    congr 1
    rw [hD, inf_comm]
  have hD' : Nat.card (G ⧸ P) = D.relIndex V * (V ⊔ P).index := by
    have h := Subgroup.relIndex_mul_index (H := P) (K := V ⊔ P) le_sup_right
    rw [hDrel] at h
    exact h.symm
  -- `Q = G/V` is finite
  have hQfin : Finite Q := Subgroup.finiteIndex_iff_finite_quotient.mp hV
  haveI := hQfin
  haveI : Nonempty ↥Qpow := ⟨⟨1, Qpow.one_mem⟩⟩
  haveI : Nonempty ↥Qtors := ⟨⟨1, Qtors.one_mem⟩⟩
  have hQpow_pos : 0 < Nat.card Qpow := Nat.card_pos
  -- `(preimage of V) / V ≅ Q[ℓ]`
  let ψ : ↥S →* Q := (QuotientGroup.mk' V).comp S.subtype
  have hψker : ψ.ker = V.subgroupOf S := Subgroup.ext fun x => by
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk' V) (S.subtype x) = 1 ↔ (x : G) ∈ V
    rw [QuotientGroup.mk'_apply]
    exact QuotientGroup.eq_one_iff (x : G)
  have hψrange : ψ.range = Qtors := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨s, rfl⟩
      rw [hQtors, MonoidHom.mem_ker]
      show ((QuotientGroup.mk' V) (s : G)) ^ ℓ = 1
      rw [← map_pow, QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff ((s : G) ^ ℓ)).mpr (s.2)
    · intro y hy
      rw [hQtors, MonoidHom.mem_ker] at hy
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective V y
      refine ⟨⟨g, ?_⟩, rfl⟩
      rw [hS, Subgroup.mem_comap]
      show g ^ ℓ ∈ V
      rw [← QuotientGroup.eq_one_iff (g ^ ℓ)]
      rw [← QuotientGroup.mk'_apply, map_pow]
      exact hy
  have hiso : (↥S ⧸ V.subgroupOf S) ≃* ↥Qtors :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hψrange))
  have hE2 : Nat.card (↥S ⧸ V.subgroupOf S) = Nat.card Qtors := Nat.card_congr hiso.toEquiv
  have hcardQ : Nat.card (↥S ⧸ V.subgroupOf S) ≠ 0 := by
    rw [hE2]
    exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  haveI : Finite (↥S ⧸ V.subgroupOf S) := Nat.finite_of_card_ne_zero hcardQ
  -- `Q[ℓ]` and `Q/Q ^ ℓ` have the same order
  have hE3 : Nat.card Qtors = Nat.card (Q ⧸ Qpow) := by
    have hidx : Qtors.index = Nat.card Qpow := Subgroup.index_ker (powMonoidHom ℓ : Q →* Q)
    have h1 : Nat.card Qtors * Nat.card Qpow = Nat.card Q := by
      have h := Subgroup.card_mul_index Qtors
      rwa [hidx] at h
    have h2 : Nat.card Qpow * Nat.card (Q ⧸ Qpow) = Nat.card Q :=
      Subgroup.card_mul_index Qpow
    rw [mul_comm (Nat.card Qtors) (Nat.card Qpow)] at h1
    exact Nat.mul_left_cancel hQpow_pos (h1.trans h2.symm)
  -- `Q/Q ^ ℓ ≅ G/(V ⊔ P)`
  have hE4 : Nat.card (Q ⧸ Qpow) = Nat.card (G ⧸ (V ⊔ P)) := by
    have hmap : (V ⊔ P).map (QuotientGroup.mk' V) = Qpow := by
      have hcomp : (QuotientGroup.mk' V).comp (powMonoidHom ℓ : G →* G) =
          (powMonoidHom ℓ : Q →* Q).comp (QuotientGroup.mk' V) :=
        MonoidHom.ext fun g => by
          show (QuotientGroup.mk' V) (g ^ ℓ) = ((QuotientGroup.mk' V) g) ^ ℓ
          rw [map_pow]
      have hVbot : V.map (QuotientGroup.mk' V) = ⊥ :=
        Subgroup.map_eq_bot_iff V |>.mpr (by rw [QuotientGroup.ker_mk'])
      rw [Subgroup.map_sup, hVbot, bot_sup_eq, hP, MonoidHom.map_range, hcomp,
        ← MonoidHom.map_range, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective V),
        ← MonoidHom.range_eq_map (powMonoidHom ℓ : Q →* Q)]
    have hkey : Nat.card (Q ⧸ Qpow) = ((V ⊔ P).map (QuotientGroup.mk' V)).index :=
      (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hmap).toEquiv).symm
    rw [hkey]
    exact Subgroup.index_map_eq (V ⊔ P) (QuotientGroup.mk'_surjective V)
      (by rw [QuotientGroup.ker_mk']; exact le_sup_left)
  -- the crux: a surjection `(preimage of V)/V ↠ (V ⊓ P)/W`
  have hcrux : Nat.card (↥D ⧸ W.subgroupOf D) ≤ (V ⊔ P).index := by
    have hFD : ∀ s : ↥S, (s : G) ^ ℓ ∈ D := fun s =>
      ⟨s.2, MonoidHom.mem_range.mpr ⟨(s : G), rfl⟩⟩
    let F : ↥S →* ↥D :=
      { toFun := fun s => ⟨(s : G) ^ ℓ, hFD s⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp [mul_pow]) }
    let Φ : ↥S →* (↥D ⧸ W.subgroupOf D) := (QuotientGroup.mk' (W.subgroupOf D)).comp F
    have hΦker : V.subgroupOf S ≤ Φ.ker := by
      intro s hs
      rw [Subgroup.mem_subgroupOf] at hs
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf, hW, Subgroup.mem_map]
      refine ⟨⟨(s : G), hs⟩ ^ ℓ, ?_, ?_⟩
      · exact MonoidHom.mem_range.mpr ⟨⟨(s : G), hs⟩, rfl⟩
      · rw [map_pow]
        rfl
    let Fbar : (↥S ⧸ V.subgroupOf S) →* (↥D ⧸ W.subgroupOf D) :=
      QuotientGroup.lift (V.subgroupOf S) Φ hΦker
    have hsurj : Function.Surjective Fbar := by
      rintro x
      obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp
        (show (d : G) ∈ (powMonoidHom ℓ : G →* G).range from by rw [← hP]; exact d.2.2)
      have hgS : g ∈ S := by
        rw [hS, Subgroup.mem_comap]
        rw [show (powMonoidHom ℓ : G →* G) g = (d : G) from hg]
        exact d.2.1
      refine ⟨QuotientGroup.mk ⟨g, hgS⟩, ?_⟩
      dsimp only [Fbar, Φ]
      rw [QuotientGroup.lift_mk, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      have hFeq : F ⟨g, hgS⟩ = d := Subtype.ext hg
      rw [hFeq]
    calc Nat.card (↥D ⧸ W.subgroupOf D) ≤ Nat.card (↥S ⧸ V.subgroupOf S) :=
          Nat.card_le_card_of_surjective Fbar hsurj
      _ = Nat.card Qtors := hE2
      _ = Nat.card (Q ⧸ Qpow) := hE3
      _ = Nat.card (G ⧸ (V ⊔ P)) := hE4
      _ = (V ⊔ P).index := rfl
  -- assemble
  have hmain : Nat.card (↥V ⧸ W') ≤ Nat.card (G ⧸ P) :=
    calc Nat.card (↥V ⧸ W') = W.relIndex D * D.relIndex V := hC
      _ = Nat.card (↥D ⧸ W.subgroupOf D) * D.relIndex V := rfl
      _ ≤ (V ⊔ P).index * D.relIndex V := Nat.mul_le_mul_right _ hcrux
      _ = D.relIndex V * (V ⊔ P).index := by rw [mul_comm]
      _ = Nat.card (G ⧸ P) := hD'.symm
  exact hmain

end NK.LocalCFT.Units
