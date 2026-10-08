import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.exists_PSU3_of_card_sylow_eq_cube
import Submission.Work.PSU3.StageB.isSplitRankOne_map_of_surjective
import Submission.Work.PSU3.StageA.centD_le_W_psu3Model
import Submission.Work.Models.ModelData.psu3ModelData_data
import Submission.Work.PSU3.Model.psu3_isSplitRankOne
import Submission.Work.PSU3.BenderST.split_datum_conj_standard
import Submission.Work.PSU3.StageB.NotFpfStep4.WTorusLift
import Submission.Work.PSU3.ModelCentralizer.involution_psu3B_eq_image_uUg
import Submission.Work.PSU3.ModelCentralizer.exists_suTgSU_of_mem_psu3T_centralizes_weyl

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageB.NotFpfStep2

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type*} [Group G]

/-! ## 1.  The target statement, and its invariance under conjugation and isomorphism

The conclusion of the node is a statement about a *datum* `(B, w)`: `centD B w` centralises
`⟨Inv B⟩`.  The reduction steps below (conjugating the datum, pulling it back along a group
isomorphism) are elementary but are recorded once and for all. -/

/-- **The target statement for a datum `(B, w)`.** -/
def Statement (G : Type*) [Group G] (B : Subgroup G) (w : G) : Prop :=
  centD B w ≤ Subgroup.centralizer (Subgroup.closure (involutions (B : Set G)) : Set G)

/-- The target statement is invariant under conjugation of the datum `(B, w)`. -/
theorem conj_centD_le_centralizer_closure_involutions (g : G) {B : Subgroup G} {w : G}
    (h : centD B w ≤ Subgroup.centralizer
      (Subgroup.closure (involutions (B : Set G)) : Set G)) :
    centD (conj g B) (MulAut.conj g w) ≤
      Subgroup.centralizer (Subgroup.closure (involutions (conj g B : Set G)) : Set G) := by
  have hmap : Subgroup.closure (involutions (conj g B : Set G))
      = (Subgroup.closure (involutions (B : Set G))).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_closure, Work.Models.involutions_conj]
    rfl
  intro x hx
  obtain ⟨hx2, hxc⟩ := Subgroup.mem_inf.mp hx
  -- `g⁻¹ x g` lies in `centD B w`
  have hx2' : g⁻¹ * x * g ∈ twoPoint B w := by
    have h' : x ∈ conj g (twoPoint B (g⁻¹ * MulAut.conj g w * g)) := by
      rw [← Work.Models.twoPoint_conj_conj]
      exact hx2
    rw [show g⁻¹ * MulAut.conj g w * g = w by rw [MulAut.conj_apply]; group] at h'
    exact Work.Models.mem_conj_iff.mp h'
  have hxc' : g⁻¹ * x * g ∈ Subgroup.centralizer ({w} : Set G) := by
    have hcomm : MulAut.conj g w * x = x * MulAut.conj g w :=
      hxc (MulAut.conj g w) (Set.mem_singleton _)
    rw [MulAut.conj_apply] at hcomm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc w * (g⁻¹ * x * g) = g⁻¹ * ((g * w * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * w * g⁻¹)) * g := by rw [hcomm]
      _ = (g⁻¹ * x * g) * w := by group
  have hyC : g⁻¹ * x * g ∈ centD B w := Subgroup.mem_inf.mpr ⟨hx2', hxc'⟩
  have hy := h hyC
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro s hs
  have hs' : g⁻¹ * s * g ∈ Subgroup.closure (involutions (B : Set G)) := by
    rw [hmap] at hs
    exact Work.Models.mem_conj_iff.mp hs
  have h1 := hy (g⁻¹ * s * g) hs'
  calc s * x = g * (g⁻¹ * s * g) * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = g * ((g⁻¹ * s * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * x * g) * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
    _ = x * s := by group

/-- The target statement pulls back along a group isomorphism. -/
theorem centD_le_centralizer_closure_involutions_of_map {G' : Type*} [Group G'] (e : G ≃* G')
    {B : Subgroup G} {w : G}
    (h : centD (B.map e.toMonoidHom) (e w) ≤ Subgroup.centralizer
      (Subgroup.closure (involutions ((B.map e.toMonoidHom : Subgroup G') : Set G')) :
        Set G')) :
    centD B w ≤ Subgroup.centralizer
      (Subgroup.closure (involutions (B : Set G)) : Set G) := by
  have hmap : Subgroup.closure (involutions ((B.map e.toMonoidHom : Subgroup G') : Set G'))
      = (Subgroup.closure (involutions (B : Set G))).map e.toMonoidHom := by
    rw [MonoidHom.map_closure, Work.PSU3.BenderST.involutions_map_eq]
    rfl
  intro x hx
  obtain ⟨hx2, hxc⟩ := Subgroup.mem_inf.mp hx
  have hex : e x ∈ centD (B.map e.toMonoidHom) (e w) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Work.PSU3.BenderST.twoPoint_map]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hx2
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h1 : w * x = x * w := (Subgroup.mem_centralizer_iff.mp hxc) w (Set.mem_singleton w)
      rw [← map_mul, ← map_mul, h1]
  have hcx := h hex
  rw [Subgroup.mem_centralizer_iff] at hcx ⊢
  intro s hs
  have hs' : e s ∈ Subgroup.closure (involutions ((B.map e.toMonoidHom : Subgroup G') :
      Set G')) := by
    rw [hmap]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hs
  exact e.injective (by rw [map_mul, map_mul]; exact hcx (e s) hs')

/-! ## 2.  The torus element `t(a)` with `a^{q+1} = 1` centralises `u(0,c)` -/

/-- For `a^{q+1} = 1` and `c` in the fixed field, the torus element `suTgSU n a` centralises
`u(0,c)` (`suTg_conj_suUg` with `b = 0` and `a^{q+1} = 1`). -/
theorem suTgSU_conj_uUg_zero {n : ℕ} {a : (Submission.PSU3.F n)ˣ} {c : Submission.PSU3.F n}
    (hc : c ^ (2 ^ n) = c)
    (ha : (a : Submission.PSU3.F n) ^ (2 ^ n + 1) = 1) :
    Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n a) *
        Submission.PSU3.psu3Hom n ⟨Submission.PSU3.suUg n 0 c,
          Submission.PSU3.suU_le_SU3 n (Submission.PSU3.suUg_zero_mem n c hc)⟩ *
        (Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n a))⁻¹
      = Submission.PSU3.psu3Hom n ⟨Submission.PSU3.suUg n 0 c,
          Submission.PSU3.suU_le_SU3 n (Submission.PSU3.suUg_zero_mem n c hc)⟩ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show Submission.PSU3.suTg n a * Submission.PSU3.suUg n 0 c * (Submission.PSU3.suTg n a)⁻¹
      = Submission.PSU3.suUg n 0 c
  rw [Submission.PSU3.suTg_conj_suUg]
  have hkey : (a : Submission.PSU3.F n) * c * (a : Submission.PSU3.F n) ^ (2 ^ n) = c := by
    have hmul : (a : Submission.PSU3.F n) ^ (2 ^ n) * (a : Submission.PSU3.F n) = 1 := by
      rw [← pow_succ]
      exact ha
    have haq : (a : Submission.PSU3.F n) ^ (2 ^ n) = ((a : Submission.PSU3.F n))⁻¹ :=
      eq_inv_of_mul_eq_one_left hmul
    rw [haq, mul_comm (a : Submission.PSU3.F n) c, mul_assoc,
      mul_inv_cancel₀ (Units.ne_zero a), mul_one]
  simp only [mul_zero, zero_mul, hkey]

/-! ## 3.  The two model computations (proved in `Work.PSU3.ModelCentralizer`) -/

/-- **Model input (i).**  Every involution of the Borel `psu3B n` is the image of a unipotent
element `u(0,c)` with `c` in the fixed field of the Frobenius. -/
def InvBorelUnipotent (n : ℕ) : Prop :=
  ∀ s : PSU3Model n, s ∈ Submission.PSU3.psu3B n → orderOf s = 2 →
    ∃ (c : Submission.PSU3.F n) (hc : c ^ (2 ^ n) = c),
      s = Submission.PSU3.psu3Hom n ⟨Submission.PSU3.suUg n 0 c,
        Submission.PSU3.suU_le_SU3 n (Submission.PSU3.suUg_zero_mem n c hc)⟩

/-- **Model input (ii).**  The centraliser of the Weyl element in the maximal torus is the
image of `{a : a^{q+1} = 1}`. -/
def TorusCentralizerWeyl (n : ℕ) : Prop :=
  ∀ x : PSU3Model n, x ∈ Submission.PSU3.psu3T n →
    x * Submission.PSU3.psu3Weyl n = Submission.PSU3.psu3Weyl n * x →
    ∃ a : (Submission.PSU3.F n)ˣ,
      x = Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n a) ∧
        (a : Submission.PSU3.F n) ^ (2 ^ n + 1) = 1


/-- **The node in the model, standard datum.**  `centD B̄ w̄` centralises `⟨Inv B̄⟩` in
`PSU(3,2ⁿ)`: `x ∈ centD B̄ w̄` lies in the torus `psu3T n` and commutes with the Weyl involution,
so `x = psu3Hom (suTgSU a)` with `a^{q+1} = 1`; the torus element `t(a)` centralises `u(0,c)` for
every `c` in the fixed field, and every involution of `B̄` is of that form. -/
theorem psu3_standard_statement {n : ℕ} (hn : 2 ≤ n) (hinv : InvBorelUnipotent n)
    (htor : TorusCentralizerWeyl n) :
    centD (Submission.PSU3.psu3B n) (Submission.PSU3.psu3Weyl n) ≤
      Subgroup.centralizer (Subgroup.closure
        (involutions (Submission.PSU3.psu3B n : Set (PSU3Model n))) :
        Set (PSU3Model n)) := by
  intro x hx
  obtain ⟨hx2, hxc⟩ := Subgroup.mem_inf.mp hx
  have hxT : x ∈ Submission.PSU3.psu3T n := by
    rw [← Work.PSU3.Model.twoPoint_psu3B_psu3Weyl n]
    exact hx2
  have hxcw : x * Submission.PSU3.psu3Weyl n = Submission.PSU3.psu3Weyl n * x :=
    ((Subgroup.mem_centralizer_iff.mp hxc) _ (Set.mem_singleton _)).symm
  obtain ⟨a, haeq, haq⟩ := htor x hxT hxcw
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  suffices hcl : Subgroup.closure (involutions (Submission.PSU3.psu3B n : Set (PSU3Model n))) ≤
      Subgroup.centralizer ({x} : Set (PSU3Model n)) by
    exact ((Subgroup.mem_centralizer_iff.mp (hcl hs)) x (Set.mem_singleton x)).symm
  rw [Subgroup.closure_le]
  intro t ht
  rw [Work.Models.mem_involutions_iff] at ht
  obtain ⟨c, hc, htc⟩ := hinv t ht.1 ht.2
  show t ∈ Subgroup.centralizer ({x} : Set (PSU3Model n))
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  rw [ha]
  have h1 := suTgSU_conj_uUg_zero (n := n) hc haq
  rw [← haeq, ← htc] at h1
  calc x * t = (x * t * x⁻¹) * x := by group
    _ = t * x := by rw [h1]

/-- **The node in the model, any split rank-one datum.**  In `PSU(3,2ⁿ)`, for an arbitrary split
rank-one datum `(B, U, w)`, `centD B w` centralises `⟨Inv B⟩`.

`modelDataBorel` attaches to `B` a `ModelData` `P`; `eq_U_of_isSplitRankOne` gives `U = P.U`, so
`w` is a datum on `(P.B, P.U)`.  `split_datum_conj_standard` conjugates both the standard datum
`(P.B, P.U, P.w)` of `P` and `(P.B, P.U, w)` into the fixed `ModelData`; conjugating the
standard `(psu3B n, psu3Weyl n)` statement (first application, with the `psu3BenderPair`) and
then conjugating back (second application, with `P`) gives the claim. -/
theorem psu3_datum_statement {n : ℕ} (hn : 2 ≤ n) (hinv : InvBorelUnipotent n)
    (htor : TorusCentralizerWeyl n) {B U : Subgroup (PSU3Model n)} {w : PSU3Model n}
    (h : IsSplitRankOne B U w) :
    centD B w ≤ Subgroup.centralizer (Subgroup.closure
      (involutions (B : Set (PSU3Model n))) : Set (PSU3Model n)) := by
  have hstd0 := psu3_standard_statement hn hinv htor
  obtain ⟨P, hPB⟩ := Work.PSU3.StageA.modelDataBorel
    (Submission.PSU3.PSU3Model_isSimpleBenderGroup n hn) h.stronglyEmbedded
  have hPB' : IsSplitRankOne P.B U w := hPB.symm ▸ h
  have hU : U = P.U := Work.Models.Abstract.eq_U_of_isSplitRankOne P.toBenderPair hPB'
  have hPBU : IsSplitRankOne P.B P.U w := hU ▸ hPB'
  have hstd : IsSplitRankOne P.B P.U P.w :=
    Work.PSU3.BenderST.benderPair_isSplitRankOne P.toBenderPair P.hww
  -- the standard datum of `P` is a conjugate of the standard `PSU(3,2ⁿ)` datum
  have hP : centD P.B P.w ≤ Subgroup.centralizer (Subgroup.closure
      (involutions (P.B : Set (PSU3Model n))) : Set (PSU3Model n)) := by
    obtain ⟨h, hhB, _hhU, hhw⟩ := Work.PSU3.BenderST.split_datum_conj_standard
      (Submission.PSU3.psu3BenderPair n hn) (Work.PSU3.Model.psu3_isSplitRankOne n hn) hstd
    have hhB' : conj h P.B = Submission.PSU3.psu3B n := hhB
    have hhw' : MulAut.conj h P.w = Submission.PSU3.psu3Weyl n := hhw
    have h1 := conj_centD_le_centralizer_closure_involutions h⁻¹ hstd0
    have hconjB : conj h⁻¹ (Submission.PSU3.psu3B n) = P.B := by
      have h3 : conj h⁻¹ (conj h P.B) = P.B := Work.Models.conj_inv_conj h P.B
      rwa [hhB'] at h3
    have hconjW : MulAut.conj h⁻¹ (Submission.PSU3.psu3Weyl n) = P.w := by
      rw [← hhw', MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hconjB, hconjW] at h1
    exact h1
  -- and the datum `(P.B, w)` is a conjugate of it
  have hgoal : centD P.B w ≤ Subgroup.centralizer (Subgroup.closure
      (involutions (P.B : Set (PSU3Model n))) : Set (PSU3Model n)) := by
    obtain ⟨g, hgB, _hgU, hgw⟩ :=
      Work.PSU3.BenderST.split_datum_conj_standard P.toBenderPair hstd hPBU
    have h2 := conj_centD_le_centralizer_closure_involutions g⁻¹ hP
    have hconjB : conj g⁻¹ P.B = P.B := by
      have h3 : conj g⁻¹ (conj g P.B) = P.B := Work.Models.conj_inv_conj g P.B
      rwa [hgB] at h3
    have hconjW : MulAut.conj g⁻¹ P.w = w := by
      rw [← hgw, MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hconjB, hconjW] at h2
    exact h2
  rw [← hPB]
  exact hgoal

/-- **The `PSU(3,ℓ)`-structure fact (Peterfalvi II Ch. VII §4 (2)).**  In a simple Bender group
`Y` with split rank-one datum `(B,U,w)` whose Sylow satisfies `|U| = (|Inv B| + 1)³` (so `Y` is
`PSU(3,2ⁿ)` with `ℓ = |Inv B| + 1 = 2ⁿ`, `|U| = ℓ³`), the two-point centraliser
`V = centD B w = (B ∩ B^w) ∩ C(w)` centralises `⟨Inv B⟩ = Ω₁(U) = Z(U)`.

Hint for the proof: `exists_PSU3_of_card_sylow_eq_cube` gives `e : Y ≃* PSU3Model m` with
`|Inv B| + 1 = 2^m`; transport the statement along `e` (strong embeddedness, the split rank-one
datum and the centraliser all push through an isomorphism) and reduce, via
`Work.Models.Abstract.exists_conj_eq` + conjugacy, to the standard Borel `psu3B m`, `U = psu3U m`
(`Work.Models.Abstract.eq_U_of_isSplitRankOne`), where `centD psu3B w̄ = C_{psu3T}(w̄)` for a Weyl
element `w̄ ∈ N(psu3T)`.  In the model use `Submission.PSU3.suSg_conj_suTg`
(`Models/Port/PSU3/Bruhat.lean`: `w̄ · t(a) · w̄ = t(a^{-q})`), so `C_{psu3T}(w̄)` is (the image
of) `{a : a^{q+1} = 1}`, and `Submission.PSU3.suTg_conj_suUg` /
`Submission.PSU3.suTg_mul_suUg_zero_iff` (`Models/Port/PSU3/Borel.lean`,
`Centralizer.lean`: `t(a)·u(0,c)·t(a)⁻¹ = u(0, a^{q+1}c)`) to conclude it centralises
`psu3U0 = Z(psu3U) = ⟨Inv psu3B⟩` (`center_psu3U_eq`), noting `Inv(B) ⊆ U` since `|B : U|` is odd. -/
theorem centD_le_centralizer_involutions_of_card_cube {Y : Type} [Group Y] [Finite Y]
    (hY : LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y)
    {B U : Subgroup Y} {w : Y}
    (h : Submission.Blueprint.IsSplitRankOne B U w)
    (hcard : Nat.card ↥U = ((Submission.Blueprint.involutions (B : Set Y)).ncard + 1) ^ 3) :
    Submission.Blueprint.centD B w ≤
      Subgroup.centralizer
        (Subgroup.closure (Submission.Blueprint.involutions (B : Set Y)) : Set Y) := by
  obtain ⟨m, hm, ⟨e⟩, -⟩ := Work.PSU3.StageB.exists_PSU3_of_card_sylow_eq_cube hY h hcard
  refine centD_le_centralizer_closure_involutions_of_map e ?_
  refine psu3_datum_statement hm ?_ ?_ (Work.PSU3.BenderST.isSplitRankOne_map e h)
  · intro s hs hs2
    exact Work.PSU3.ModelCentralizer.involution_psu3B_eq_image_uUg (by omega) hs hs2
  · intro x hx hxc
    exact Work.PSU3.ModelCentralizer.exists_suTgSU_of_mem_psu3T_centralizes_weyl hx hxc

end Work.PSU3.StageB.NotFpfStep2
