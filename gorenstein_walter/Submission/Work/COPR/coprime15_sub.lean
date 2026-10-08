import Mathlib
import Submission.Work.COPR.Defs

namespace Work.COPR

/-- Bender 1981, 1.5(iii): in the situation of `coprime15_gen`, if the inversion set `I_X(s)` *is*
a subgroup `I` of `G`, then `I` is abelian, normal in `X`, and lies in the Fitting subgroup
`F(X)` (stated as `Work.GW2.fittingIn X`).  (Deliverable `Work.GW2.Coprime15Prop`, third
conjunct, of area COPR.) -/
theorem coprime15_sub (G : Type) [Group G] [Finite G] (X : Subgroup G) (s : G)
    (hs : orderOf s = 2) (hodd : Odd (Nat.card X))
    (hN : s ∈ Subgroup.normalizer (X : Set G)) :
    ∀ I : Subgroup G, (I : Set G) = Work.GW2.invSet X s →
      IsMulCommutative I ∧ (I.subgroupOf X).Normal ∧ I ≤ Work.GW2.fittingIn X := by
  -- `s` is an involution, so conjugation by `s` is an involutory automorphism `c` of `G`.
  intro I hI
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs] at h
    simpa [pow_two] using h
  let c : MulAut G := MulAut.conj s
  have hc : ∀ y : G, c y = s * y * s⁻¹ := fun y => MulAut.conj_apply s y
  have hcc : c * c = 1 := by
    have h : MulAut.conj (s * s) = MulAut.conj s * MulAut.conj s :=
      map_mul (MulAut.conj : G →* MulAut G) s s
    rw [hs2, map_one (MulAut.conj : G →* MulAut G)] at h
    exact h.symm
  have hc2 : ∀ y : G, c (c y) = y := by
    intro y
    rw [← MulAut.mul_apply, hcc]
    rfl
  -- `s` normalizes `X`, and every element of `I` is inverted by `c`.
  have hnorm : ∀ x : G, x ∈ X → s * x * s⁻¹ ∈ X := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hN x).mp hx
  have hmem : ∀ x : G, x ∈ I → x ∈ X ∧ s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    have hx' : x ∈ Work.GW2.invSet X s := by rw [← hI]; exact hx
    exact hx'
  have hIX : I ≤ X := fun x hx => (hmem x hx).1
  have hinv : ∀ x ∈ I, c x = x⁻¹ := fun x hx => (hc x).trans (hmem x hx).2
  -- (i) `I` is abelian: the inversion map on `I` is a homomorphism.
  have hcomm : IsMulCommutative I := isMulCommutative_iff.mpr (fun (x : I) (y : I) => by
    have hx := hinv x x.2
    have hy := hinv y y.2
    have hxy := hinv (x * y) (I.mul_mem x.2 y.2)
    have key : (x : G)⁻¹ * (y : G)⁻¹ = (y : G)⁻¹ * (x : G)⁻¹ := by
      calc (x : G)⁻¹ * (y : G)⁻¹
          = c (x : G) * c (y : G) := by rw [hx, hy]
        _ = c ((x : G) * (y : G)) := (map_mul c _ _).symm
        _ = ((x : G) * (y : G))⁻¹ := hxy
        _ = (y : G)⁻¹ * (x : G)⁻¹ := by rw [mul_inv_rev]
    have keyG : (x : G) * (y : G) = (y : G) * (x : G) := by
      have := congrArg (fun t : G => t⁻¹) key
      simpa [mul_inv_rev, inv_inv] using this.symm
    exact Subtype.ext keyG
  )
  have hcommG : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a := fun a ha b hb => by
    have h := (hcomm.is_comm).comm (⟨a, ha⟩ : I) (⟨b, hb⟩ : I)
    simpa using h
  -- For `b ∈ X` the element `b⁻¹ · c b` again lies in `I` (it is inverted by `c`).
  have hd : ∀ b : G, b ∈ X → b⁻¹ * c b ∈ I := by
    intro b hb
    have hbX : b⁻¹ * c b ∈ X := by
      rw [hc b]; exact X.mul_mem (X.inv_mem hb) (hnorm b hb)
    have heq : c (b⁻¹ * c b) = (b⁻¹ * c b)⁻¹ := by
      rw [map_mul, map_inv, hc2 b, mul_inv_rev, inv_inv]
    have hthis : b⁻¹ * c b ∈ Work.GW2.invSet X s :=
      ⟨hbX, (hc (b⁻¹ * c b)).symm.trans heq⟩
    rw [← hI] at hthis
    exact hthis
  -- (ii) `I` is normal in `X`: `b a b⁻¹ = (b·u) a (b·u)⁻¹` with `u = b⁻¹·c b ∈ I` centralizing `a`.
  have hnormI : (I.subgroupOf X).Normal := ⟨fun n hn g => by
    have ha : (n : G) ∈ I := Subgroup.mem_subgroupOf.mp hn
    have hb : (g : G) ∈ X := g.2
    rw [Subgroup.mem_subgroupOf]
    show ((g : G) * (n : G) * (g : G)⁻¹) ∈ I
    have hu : (g : G)⁻¹ * c (g : G) ∈ I := hd (g : G) hb
    have hua : ((g : G)⁻¹ * c (g : G)) * (n : G)⁻¹ * ((g : G)⁻¹ * c (g : G))⁻¹
        = (n : G)⁻¹ := by
      have h := hcommG _ hu _ (I.inv_mem ha)
      rw [h]; group
    have hmain : c ((g : G) * (n : G) * (g : G)⁻¹)
        = ((g : G) * (n : G) * (g : G)⁻¹)⁻¹ := by
      have step1 : c ((g : G) * (n : G) * (g : G)⁻¹)
          = c (g : G) * c (n : G) * (c (g : G))⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      have step2 : c (g : G) * c (n : G) * (c (g : G))⁻¹
          = ((g : G) * ((g : G)⁻¹ * c (g : G))) * (n : G)⁻¹
              * ((g : G) * ((g : G)⁻¹ * c (g : G)))⁻¹ := by
        rw [show (g : G) * ((g : G)⁻¹ * c (g : G)) = c (g : G) from by group]
        rw [hinv (n : G) ha]
      have step3 : ((g : G) * ((g : G)⁻¹ * c (g : G))) * (n : G)⁻¹
              * ((g : G) * ((g : G)⁻¹ * c (g : G)))⁻¹
          = (g : G) * (n : G)⁻¹ * (g : G)⁻¹ := by
        rw [show (g : G) * ((g : G)⁻¹ * c (g : G)) * (n : G)⁻¹
                  * ((g : G) * ((g : G)⁻¹ * c (g : G)))⁻¹
                = (g : G) * (((g : G)⁻¹ * c (g : G)) * (n : G)⁻¹
                  * ((g : G)⁻¹ * c (g : G))⁻¹) * (g : G)⁻¹ from by group]
        rw [hua]
      have step4 : (g : G) * (n : G)⁻¹ * (g : G)⁻¹
          = ((g : G) * (n : G) * (g : G)⁻¹)⁻¹ := by group
      exact step1.trans (step2.trans (step3.trans step4))
    have hthis : ((g : G) * (n : G) * (g : G)⁻¹) ∈ Work.GW2.invSet X s :=
      ⟨X.mul_mem (X.mul_mem hb (hIX ha)) (X.inv_mem hb),
        (hc ((g : G) * (n : G) * (g : G)⁻¹)).symm.trans hmain⟩
    rw [← hI] at hthis
    exact hthis
  ⟩
  refine ⟨hcomm, hnormI, ?_⟩
  -- (iii) `I` is abelian normal in `X`, hence nilpotent, so it lies in `F(X)`.
  have hnilpI : Group.IsNilpotent ↥I := CommGroup.isNilpotent
  have hnilpK : Group.IsNilpotent ↥(I.subgroupOf X) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hIX)).mpr hnilpI
  have hKle : I.subgroupOf X ≤ Work.GW2.fitting ↥X := by
    rw [Work.GW2.fitting]
    haveI : (I.subgroupOf X).Normal := hnormI
    rw [Subgroup.normal_le_normalCore]
    exact le_sSup ⟨hnormI, hnilpK⟩
  have hmap : (I.subgroupOf X).map X.subtype = I := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
    exact hIX
  rw [Work.GW2.fittingIn, ← hmap]
  exact Subgroup.map_mono hKle

end Work.COPR
