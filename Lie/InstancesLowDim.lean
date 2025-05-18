import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Lie.Semidirect
import Mathlib.Algebra.Lie.DirectSum
import Lie.GeneralResults
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import Lie.InstancesConstructions

open Module
open Submodule

namespace LieAlgebra

namespace Dim2
section dimension_two

variable (K : Type*) [CommRing K]

abbrev Abelian := mkAbelian K (Fin 2 → K)

def Affine := Fin 2 → K

instance : LieRing (Affine K) := {
  (inferInstance : AddCommGroup (Fin 2 → K)) with
  bracket := fun l r ↦ ![0, l 0 * r 1 - r 0 * l 1]
  add_lie := by
    intro x y z
    simp [Affine]
    ext _; ring_nf
  lie_add := by
    intro x y z
    simp [Affine]
    ext _; ring_nf
  lie_self := by
    intro x
    simp [Affine]
  leibniz_lie := by
    intro x y z
    simp [Affine]
    ext _; ring_nf
}

theorem Affine.bracket {l r : Affine K} : ⁅l , r⁆ = ![0, l 0 * r 1 - r 0 * l 1] := by
  rfl

instance : LieAlgebra K (Affine K) := {
  (inferInstance : Module K (Fin 2 → K)) with
  lie_smul := by
    intro t x y
    simp [Affine, Bracket.bracket]
    ext _; ring_nf
}

end dimension_two

section dim2_affine_lemmas

namespace Affine

variable {K : Type*} [Field K]

/--In this section we prove that Dim2.Affine is isomorphic to the semidirect product gl(K) ⋉ K,
   where K is the 1-dimensional vector space over K -/

def equivToLieAlgOfAffineEquiv : 𝔞𝔣𝔣 K K ≃ₗ⁅K⁆ Affine K := {
  toFun := fun ⟨f, x⟩ ↦ ![f 1, x]
  invFun := fun v ↦ ⟨v 0 • LinearMap.id, v 1⟩
  left_inv := by
    intro ⟨f, x⟩
    ext
    · simp only [Matrix.cons_val_zero, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      smul_eq_mul, mul_one]
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
  right_inv := by
    intro v
    unfold Affine
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul, mul_one]
    exact List.ofFn_inj.mp rfl
  map_add' := by
    intro ⟨f, x⟩ ⟨g, y⟩
    unfold Affine
    ext i
    simp only [LinearMap.add_apply, Pi.add_apply]
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  map_smul' := by
    intro a ⟨f, x⟩
    unfold Affine
    ext i
    simp only [LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Pi.smul_apply]
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  map_lie' := by
    intro ⟨f, x⟩ ⟨g, y⟩
    simp [Affine.bracket]
    unfold Affine ofAffineEquivAux
    rw [LieEquiv.coe_toLieHom]
    unfold mkAbelian at *
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero]
      rw [← mul_one (g 1), ← mul_one (f 1), ← smul_eq_mul, ← smul_eq_mul, map_smul, map_smul,
        smul_eq_mul, smul_eq_mul, mul_comm, sub_self]
    · simp only [Fin.mk_one, Matrix.cons_val_one,
      Matrix.head_cons, Abelian.DerivationCoeFun]
}

def equivToRealHyperbolic : Affine K ≃ₗ⁅K⁆ 𝔥𝔶𝔭 2 K:={
  toFun := fun v ↦ ⟨v 0, ![v 1]⟩
  map_add' := by
    intro x y
    simp only [Affine, RealHyperbolic, Pi.add_apply]
    ext
    · rfl
    · simp only [mkAbelian]
      simp only [Fin.isValue, LieSemidirectProduct.add_right, Nat.add_one_sub_one, Matrix.add_cons,
        Matrix.head_cons, Matrix.tail_cons, Matrix.empty_add_empty]
  map_smul' := by
    intro a x
    ext
    · rfl
    · simp only [mkAbelian,Nat.add_one_sub_one, Fin.isValue, RingHom.id_apply,
      LieSemidirectProduct.smul_right,Fin.isValue, Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty]
      rfl
  map_lie' := by
    intro x y
    simp only [Bracket.bracket, Nat.add_one_sub_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, add_zero]
    simp only [RealHyperbolicAux, RealHyperbolicAux']
    ext
    · simp only [Fin.isValue, mul_comm, sub_self]
    · simp only [Fin.isValue, LieHom.coe_comp, LieHom.coe_smulRight, Function.comp_apply,
      LieHom.map_smul, LieDerivation.coe_smul, Abelian.DerivationCoeFun', LinearMap.id_coe,
      Pi.smul_apply, id_eq]
      simp only [mkAbelian,Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, LieHom.smulRight_apply,
       LinearMap.smul_apply,LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_cons, smul_eq_mul,
       mul_zero, Matrix.smul_empty, Pi.sub_apply, sub_self, Pi.neg_apply, neg_zero, neg_mul]
      simp only [Fin.isValue, Matrix.sub_cons, Matrix.head_cons, Matrix.tail_cons, sub_self,
        Matrix.zero_empty]
  invFun := fun ⟨k, v⟩ ↦ ![k, v 0]
  left_inv := by
    intro x
    simp only [Fin.isValue, Matrix.cons_val_fin_one]
    exact List.ofFn_inj.mp rfl
  right_inv := by
    intro ⟨k, v⟩
    simp only [Nat.add_one_sub_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    ext
    · rfl
    · simp only [mkAbelian]
      exact List.ofFn_inj.mp rfl
}

end Affine
end dim2_affine_lemmas
end Dim2

namespace Dim3
section dimension_three

variable (K : Type*) [CommRing K]

/-- The three-dimensional abelian Lie algebra. -/
abbrev Abelian := mkAbelian K (Fin 3 → K)

/-- The three-dimensional Heisenberg Lie algebra. -/
def Heisenberg := Fin 3 → K

instance : LieRing (Heisenberg K) := {
  (inferInstance : AddCommGroup (Fin 3 → K)) with
  bracket := fun l r ↦ ![l 1 * r 2 - r 1 * l 2, (0 : K), (0 : K)]
  add_lie := by
    intro x y z
    simp [Heisenberg]
    ext _; ring_nf
  lie_add := by
    intro x y z
    simp [Heisenberg]
    ext _; ring_nf
  lie_self := by
    intro x
    simp [Heisenberg]
  leibniz_lie := by
    intro x y z
    simp [Heisenberg]
}

theorem Heisenberg.bracket {l r : Heisenberg K} : ⁅l, r⁆ = ![l 1 * r 2 - r 1 * l 2, (0 : K), (0 : K)] := by
  rfl

instance : LieAlgebra K (Heisenberg K) := {
  (inferInstance : Module K (Fin 3 → K)) with
  lie_smul := by
    intro t x y
    simp [Heisenberg, Bracket.bracket]
    ext _; ring_nf
}

/-- The three-dimensional Lie algebra which has one-dimensional commutator and is not nilpotent. -/
def AffinePlusAbelian := Fin 3 → K

instance : LieRing (AffinePlusAbelian K) := {
  (inferInstance : AddCommGroup (Fin 3 → K)) with
  bracket := fun l r ↦  ![0, l 1 * r 2 - r 1 * l 2, 0]
  add_lie := by
    intro x y z
    simp [AffinePlusAbelian]
    ext _; ring_nf
  lie_add := by
    intro x y z
    simp [AffinePlusAbelian]
    ext _; ring_nf
  lie_self := by
    intro x
    simp [AffinePlusAbelian]
  leibniz_lie := by
    intro x y z
    simp [AffinePlusAbelian]
    ext _; ring_nf
}

theorem AffinePlusAbelian.bracket {l r : AffinePlusAbelian K} : ⁅l , r⁆ = ![(0 : K), l 1 * r 2 - r 1 * l 2, (0 : K)] := by
  rfl

instance : LieAlgebra K (AffinePlusAbelian K):= {
  (inferInstance : Module K (Fin 3 → K)) with
  lie_smul := by
    intro t x y
    simp [AffinePlusAbelian,Bracket.bracket]
    ext _; ring_nf
}

/-- The three-dimensional solvable Lie algebra associated to real hyperbolic space. -/
def Hyperbolic := Fin 3 → K

instance : LieRing (Hyperbolic K) := {
  (inferInstance : AddCommGroup (Fin 3 → K)) with
  bracket := fun l r ↦ ![0, (l 0 * r 1 - r 0 *l 1), (l 0 * r 2 - r 0 * l 2)]
  add_lie := by
    intro x y z
    simp [Hyperbolic]
    ext _; ring_nf
  lie_add := by
    intro x y z
    simp [Hyperbolic]
    ext _; ring_nf
  lie_self := by
    intro x
    simp [Hyperbolic]
  leibniz_lie := by
    intro x y z
    simp [Hyperbolic]
    ext _; ring_nf
}

instance : LieAlgebra K (Hyperbolic K) := {
  (inferInstance : Module K (Fin 3 → K)) with
  lie_smul := by
    intro t x y
    simp [Hyperbolic, Bracket.bracket]
    ext _; ring_nf
}

theorem Hyperbolic.bracket (l r : Hyperbolic K) :
    ⁅l, r⁆ = ![0, (l 0 * r 1 - r 0 * l 1), (l 0 * r 2 - r 0 * l 2)] := by
  rfl

/-- The two-parameter family of solvable Lie algebras appearing in the classification of 3-dimensional Lie algebras. -/
def Family (_ _ : K) := Fin 3 → K

instance (α : K) (β : K): LieRing (Family K α β) := {
  (inferInstance : AddCommGroup (Fin 3 → K)) with
  bracket := fun l r ↦ ![0, (l 0 * r 2 - l 2 * r 0) * α, (l 0 * r 2 - l 2 * r 0) * β + l 0 * r 1 - l 1 * r 0]
  add_lie := by
    intro x y z
    simp [Family]
    ext _; ring_nf
  lie_add := by
    intro x y z
    simp [Family]
    ext _; ring_nf
  lie_self := by
    intro x
    simp only [Family]
    ring_nf
    exact List.ofFn_inj.mp rfl
  leibniz_lie := by
    intro x y z
    simp [Family]
    ext _; ring_nf
}

instance (α : K) (β : K): LieAlgebra K (Family K α β) := {
  (inferInstance : Module K (Fin 3 → K)) with
  lie_smul := by
    intro t x y
    simp [Family, Bracket.bracket]
    ext _; ring_nf
}

theorem Family.bracket (α β : K) (l r : Family _ α β) :
    ⁅l, r⁆ = ![0, (l 0 * r 2 - l 2 * r 0) * α, (l 0 * r 2 - l 2 * r 0) * β + l 0 * r 1 - l 1 * r 0] := by
  rfl

end dimension_three

section dim3_lemmas

variable {K : Type*} [CommRing K]

def Heisenberg.semidirectAux' : End K (Dim2.Abelian K) := {
  toFun := fun v ↦ ![v 1, 0]
  map_add' := by
    intro x y
    simp only [mkAbelian, Pi.add_apply, Matrix.add_cons, Matrix.head_cons,
      Matrix.tail_cons, add_zero, Matrix.empty_add_empty, mul_add]
  map_smul' := by
    intro a x
    simp only [mkAbelian, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Matrix.smul_cons, mul_zero, Matrix.smul_empty]
}

def Heisenberg.semidirectAux : K →ₗ⁅K⁆ LieDerivation K (Dim2.Abelian K) (Dim2.Abelian K) :=
  LieHom.comp (Abelian.DerivationOfLinearMap K (Dim2.Abelian K)) (LieHom.smulRight Heisenberg.semidirectAux')

/-- The three-dimensional Heisenberg Lie algebra over `K` is isomorphic to a semidirect product of `K`
    with the two-dimensional abelian Lie algebra. -/
def Heisenberg.equivToSemidirect : Heisenberg K ≃ₗ⁅K⁆ K ⋉[Heisenberg.semidirectAux] Dim2.Abelian K := {
  toFun := fun v ↦ ⟨v 1, ![v 0, v 2]⟩
  map_add' := by
    intro x y
    rw [Prod.add_def]
    simp only [Heisenberg, Pi.add_apply]
    ext
    · rfl
    · simp only [mkAbelian]
      ext i
      fin_cases i
      · simp only [Fin.zero_eta,
        Matrix.cons_val_zero, Pi.add_apply]
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply]
  map_smul' := by
    intro a x
    rw [Prod.smul_def]
    simp only [Heisenberg, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ext
    · rfl
    · simp only [mkAbelian, Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty]
  map_lie' := by
    intro x y
    simp only [semidirectAux, semidirectAux', Bracket.bracket, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      mul_comm, sub_self, LieHom.coe_comp, LieHom.coe_mk, Function.comp_apply, LieHom.map_smul, LieDerivation.coe_smul,
      Abelian.DerivationCoeFun', LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Matrix.smul_cons, smul_eq_mul, zero_mul,
      Matrix.smul_empty, add_zero]
    ext
    · simp only
    · simp only [mkAbelian]
      ext i
      fin_cases i
      · simp only [Fin.zero_eta,
        Matrix.cons_val_zero, LieHom.smulRight_apply, LinearMap.smul_apply, LinearMap.coe_mk,
        AddHom.coe_mk, Matrix.cons_val_one, Matrix.head_cons, Matrix.smul_cons, smul_eq_mul,
        mul_zero, Matrix.smul_empty, Pi.sub_apply]
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, LieHom.coe_smulRight, LinearMap.smul_apply,
        LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty,
        Pi.sub_apply, sub_self]
  invFun := fun ⟨k, v⟩ ↦ ![v 0, k, v 1]
  left_inv := by
    intro x
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Heisenberg]
    exact List.ofFn_inj.mp rfl
  right_inv := by
    intro ⟨k, v⟩
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons]
    ext
    · rfl
    · simp only [mkAbelian]
      exact List.ofFn_inj.mp rfl
}

/-- The three-dimensional Lie algebra `AffinePlusAbelian K` is indeed isomorphic to the direct sum/product of `K`
    with `LieAlgebra.Dim2.Affine K`. -/
def AffinePlusAbelian.equivToDirectSum : AffinePlusAbelian K ≃ₗ⁅K⁆ K × Dim2.Affine K := {
  toFun := fun v ↦ ⟨v 0, ![-v 2, v 1]⟩
  map_add' := by
    intro x y
    simp only [Dim2.Affine, AffinePlusAbelian, Pi.add_apply, neg_add,
      Prod.mk_add_mk, Matrix.add_cons, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_add_empty,
      Prod.mk.injEq, true_and]
  map_smul' := by
    intro a x
    simp only [Dim2.Affine, AffinePlusAbelian, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Prod.smul_mk, Matrix.smul_cons, mul_neg, Matrix.smul_empty]
  map_lie' := by
    intro x y
    simp only [Bracket.bracket, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_one,
      neg_sub, mul_neg, sub_neg_eq_add, Prod.mk.injEq]
    constructor
    · rw [mul_comm, sub_self]
    · unfold Dim2.Affine
      ext i
      simp only [neg_zero, neg_mul, sub_neg_eq_add]
      fin_cases i
      · rfl
      · simp only [ Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]
        ring_nf
  invFun := fun ⟨k, v⟩ ↦ ![k, v 1, -v 0]
  left_inv := by
    intro x
    simp only [AffinePlusAbelian, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_zero, neg_neg]
    exact List.ofFn_inj.mp rfl
  right_inv := by
    intro ⟨k, v⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Nat.succ_eq_add_one,
      Matrix.tail_cons, Matrix.head_cons, neg_neg, Matrix.cons_val_one,
      Prod.mk.injEq, true_and]
    exact List.ofFn_inj.mp rfl
}

def AffinePlusAbelian.semidirectAux' : End K (Dim2.Abelian K) := {
  toFun := fun v ↦ ![0, - v 1]
  map_add' := by
    intro x y
    simp only [mkAbelian, Pi.add_apply, Matrix.add_cons, Matrix.head_cons,
      Matrix.tail_cons, add_zero, Matrix.empty_add_empty, mul_add, neg_add]
  map_smul' := by
    intro a x
    simp only [mkAbelian, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Matrix.smul_cons, mul_zero, Matrix.smul_empty, mul_neg]
}

def AffinePlusAbelian.semidirectAux: K →ₗ⁅K⁆ LieDerivation K (Dim2.Abelian K) (Dim2.Abelian K) :=
  LieHom.comp (Abelian.DerivationOfLinearMap K (Dim2.Abelian K)) (LieHom.smulRight AffinePlusAbelian.semidirectAux')

/-- The three-dimensional Lie algebra `AffinePlusAbelian K` is isomorphic to a semidirect product of `K`
    with the two-dimensional abelian Lie algebra. -/
def AffinePlusAbelian.equivToSemidirect : AffinePlusAbelian K ≃ₗ⁅K⁆ K ⋉[AffinePlusAbelian.semidirectAux] Dim2.Abelian K :={
  toFun:=fun v ↦ ⟨v 2, ![v 0, - v 1]⟩
  map_add':=by
    intro x y
    rw [Prod.add_def]
    simp only [AffinePlusAbelian, Pi.add_apply]
    ext
    · rfl
    · simp only [mkAbelian]
      ext i
      fin_cases i
      · simp only [Fin.zero_eta,
        Matrix.cons_val_zero, Pi.add_apply]
      · simp only [Fin.isValue, neg_add_rev, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, add_comm]
  map_smul':=by
    intro a x
    simp only [AffinePlusAbelian]
    rw [Prod.smul_def]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ext
    · rfl
    · simp only [mkAbelian, Matrix.smul_cons, smul_eq_mul, mul_neg, Matrix.smul_empty]
  map_lie':=by
    intro x y
    simp only [semidirectAux, semidirectAux', Bracket.bracket, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      mul_comm, sub_self, LieHom.coe_comp, LieHom.coe_mk, Function.comp_apply, LieHom.map_smul, LieDerivation.coe_smul,
      Abelian.DerivationCoeFun', LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Matrix.smul_cons, smul_eq_mul, zero_mul,
      Matrix.smul_empty, add_zero]
    ext
    · simp only
    · simp only [mkAbelian]
      ext i
      fin_cases i
      · simp only [neg_sub, Fin.zero_eta,
        Matrix.cons_val_zero, LieHom.smulRight_apply, LinearMap.smul_apply, LinearMap.coe_mk,
        AddHom.coe_mk, Matrix.cons_val_one, Matrix.head_cons, neg_neg, Matrix.smul_cons,
        smul_eq_mul, mul_zero, Matrix.smul_empty, Pi.sub_apply, sub_self]
      · simp only [neg_sub, Fin.mk_one,
        Matrix.cons_val_one, Matrix.head_cons, LieHom.smulRight_apply, LinearMap.smul_apply,
        LinearMap.coe_mk, AddHom.coe_mk, neg_neg, Matrix.smul_cons, smul_eq_mul, mul_comm, zero_mul,
        Matrix.smul_empty, Pi.sub_apply]
        simp only [Fin.isValue, Matrix.cons_val_fin_one, neg_neg]
  invFun:=fun ⟨k, v⟩ ↦ ![v 0, -v 1, k]
  left_inv:=by
    intro x
    simp only [AffinePlusAbelian, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_zero, neg_neg]
    exact List.ofFn_inj.mp rfl
  right_inv:=by
    intro ⟨k, v⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Nat.succ_eq_add_one,
      Matrix.tail_cons, Matrix.head_cons, neg_neg, Matrix.cons_val_one,
      Prod.mk.injEq, true_and]
    ext
    · rfl
    · simp only [mkAbelian]
      exact List.ofFn_inj.mp rfl
}

end dim3_lemmas

section dim3_hyperbolic_lemmas

namespace Hyperbolic

variable {K : Type*} [CommRing K]

/- In this section we study properties of the Lie algebra Hyperbolic. -/

def equivToRealHyperbolic : Hyperbolic K ≃ₗ⁅K⁆ 𝔥𝔶𝔭 3 K:={
  toFun := fun v ↦ ⟨v 0, ![v 1, v 2]⟩
  map_add' := by
    intro x y
    simp only [Hyperbolic, RealHyperbolic, Pi.add_apply]
    simp only [Nat.add_one_sub_one, Fin.isValue]
    ext
    · rfl
    · simp only [mkAbelian]
      simp only [Fin.isValue, LieSemidirectProduct.add_right, Nat.add_one_sub_one, Matrix.add_cons,
        Matrix.head_cons, Matrix.tail_cons, Matrix.empty_add_empty]
  map_smul' := by
    intro a x
    simp only [Hyperbolic]
    rw [Prod.smul_def]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ext
    · rfl
    · simp only [mkAbelian, Matrix.smul_cons, smul_eq_mul, mul_neg, Matrix.smul_empty]
  map_lie' := by
    intro x y
    simp only [Hyperbolic, RealHyperbolic, RealHyperbolicAux, RealHyperbolicAux', Bracket.bracket, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      mul_comm, sub_self, LieHom.coe_comp, LieHom.coe_mk, Function.comp_apply, LieHom.map_smul, LieDerivation.coe_smul,
      Abelian.DerivationCoeFun', LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Matrix.smul_cons, smul_eq_mul, zero_mul,
      Matrix.smul_empty, add_zero]
    ext
    · simp only
    · simp only [mkAbelian]
      simp only [Nat.add_one_sub_one, Fin.isValue, LieHom.coe_smulRight, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty, Matrix.sub_cons,
        Matrix.head_cons, Matrix.tail_cons, sub_self, Matrix.zero_empty]
  invFun := fun ⟨k, v⟩ ↦ ![k, v 0, v 1]
  left_inv := by
    intro x
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact List.ofFn_inj.mp rfl
  right_inv := by
    intro ⟨k, v⟩
    simp only [Nat.add_one_sub_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons]
    ext
    · rfl
    · simp only [mkAbelian]
      exact List.ofFn_inj.mp rfl
}

def e₁ : Hyperbolic K := ![1, 0, 0]
theorem e₁_def : (e₁ : Hyperbolic K) = ![1, 0, 0] := by
  rfl
def e₂ : Hyperbolic K := ![0, 1, 0]
theorem e₂_def : (e₂ : Hyperbolic K) = ![0, 1, 0] := by
  rfl
def e₃ : Hyperbolic K := ![0, 0, 1]
theorem e₃_def : (e₃ : Hyperbolic K) = ![0, 0, 1] := by
  rfl

theorem commutator_is_span_e₂e₃ : (commutator K (Hyperbolic K)).toSubmodule = span K {e₂,e₃} := by
  rw [commutator_eq_span]
  apply eq_of_le_of_le
  · rw [span_le]
    intro x ⟨y, z, h⟩
    rw [← h]
    rw [SetLike.mem_coe, mem_span_pair]
    use y 0 * z 1 - z 0 * y 1, y 0 * z 2 - z 0 * y 2
    unfold e₂ e₃
    rw [Hyperbolic.bracket, Matrix.smul_vec3, Matrix.smul_vec3, Matrix.vec3_add]
    simp only [smul_eq_mul, mul_zero, add_zero,
      mul_one, zero_add]
  · rw [span_le]
    refine subset_trans ?_ subset_span
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · use e₁, e₂
      rw [Hyperbolic.bracket]
      unfold e₁ e₂
      simp only [Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, mul_one, mul_zero, sub_zero, Matrix.cons_val_two,
        Matrix.tail_cons, sub_self]
    · use e₁, e₃
      rw [Hyperbolic.bracket]
      unfold e₁ e₃
      simp only [Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, mul_one, mul_zero, sub_zero, Matrix.cons_val_two,
        Matrix.tail_cons, sub_self]

theorem commutator_repr {x : Hyperbolic K} : x ∈ commutator K (Hyperbolic K) ↔ ∃ a b : K, a • e₂ + b • e₃ = x := by
  rw [← LieSubmodule.mem_toSubmodule, Hyperbolic.commutator_is_span_e₂e₃, mem_span_pair]

noncomputable def stdBasis : Basis (Fin 3) K (Hyperbolic K) := Basis.ofEquivFun (LinearEquiv.refl K (Fin 3 → K))

theorem stdBasis₁ : (stdBasis 0 : Hyperbolic K) = e₁ := by
  unfold stdBasis Hyperbolic
  rw [e₁_def]
  simp only [Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
    Nat.reduceAdd]
  ext i
  fin_cases i <;> simp

theorem stdBasis₂ : (stdBasis 1 : Hyperbolic K) = e₂ := by
  unfold stdBasis Hyperbolic
  rw [e₂_def]
  simp only [Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
    Nat.reduceAdd]
  ext i
  fin_cases i <;> simp

theorem stdBasis₃ : (stdBasis 2 : Hyperbolic K) = e₃ := by
  unfold stdBasis Hyperbolic
  rw [e₃_def]
  simp only [Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
    Nat.reduceAdd]
  ext i
  fin_cases i <;> simp

noncomputable def commutatorBasis : Basis (Fin 2) K (commutator K (Hyperbolic K)) := by
  have li : LinearIndependent K ![(e₂ : Hyperbolic K), e₃] := by
    refine LinearIndependent.pair_iff.mpr ?_
    intro s t hst
    unfold e₂ e₃ Hyperbolic at hst
    simp only [Matrix.smul_cons, smul_eq_mul, mul_zero, mul_one, Matrix.smul_empty, Matrix.add_cons,
      Matrix.head_cons, add_zero, Matrix.tail_cons, zero_add, Matrix.empty_add_empty,
      Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true, true_and] at hst
    assumption
  have li_range : Set.range ![(e₂ : Hyperbolic K), e₃] = {e₂, e₃} := by
    simp only [Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.union_singleton]
    exact Set.pair_comm e₃ e₂
  let b := Basis.span li
  rw [li_range, ← commutator_is_span_e₂e₃] at b
  exact b

theorem dim_commutator {K : Type*} [Field K] : finrank K (commutator K (Hyperbolic K)) = 2 := by
  rw [finrank_eq_card_basis commutatorBasis, Fintype.card_fin]

def adjoint (x : Hyperbolic K) := ad K (Hyperbolic K) x

def ade₁ := adjoint (e₁ : Hyperbolic K)

theorem ad_preserves_commutator (x : Hyperbolic K) : ∀ y ∈ (commutator K (Hyperbolic K)), (adjoint x) y ∈ (commutator K (Hyperbolic K)) := by
  intro y hy
  have : adjoint x y ∈ map ((ad K (Hyperbolic K)) x) ⊤ := by
    rw [Submodule.map_top, LinearMap.mem_range]
    use y
    rfl
  have := LieAlgebra.ad_into_commutator x this
  simp only [LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.mem_toSubmodule] at this
  assumption

def ad_restr (x : Hyperbolic K) : (commutator K (Hyperbolic K)) →ₗ[K] (commutator K (Hyperbolic K)) :=
  LinearMap.restrict (adjoint x) (ad_preserves_commutator x)

theorem ad_restr_apply (x : Hyperbolic K)  (y : Hyperbolic K) (hy : y ∈ (commutator K (Hyperbolic K))) :
    ad_restr x (⟨y, hy⟩ : (commutator K (Hyperbolic K))) = ⟨adjoint x y, ad_preserves_commutator x y hy⟩ :=
  rfl

theorem ad_restr_add (x y : Hyperbolic K) : ad_restr (x + y) = ad_restr x + ad_restr y := by
  ext z
  simp only [LinearMap.add_apply, LieSubmodule.coe_add]
  rw [ad_restr_apply, ad_restr_apply, ad_restr_apply]
  unfold adjoint
  simp only [LieHom.map_add, LinearMap.add_apply, ad_apply]

theorem ad_restr_smul (a : K) (x : Hyperbolic K) : ad_restr (a • x) = a • ad_restr x := by
  ext z
  simp only [LinearMap.smul_apply, LieSubmodule.coe_smul]
  rw [ad_restr_apply, ad_restr_apply]
  unfold adjoint
  simp only [LieHom.map_smul, LinearMap.smul_apply, ad_apply]

theorem lie_e₁e₂ : ⁅(e₁ : Hyperbolic K), (e₂ : Hyperbolic K)⁆ = e₂ := by
  rw [Hyperbolic.bracket, e₁_def, e₂_def]
  unfold Hyperbolic
  simp only [Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, mul_one, mul_zero, sub_zero, Matrix.cons_val_two,
    Matrix.tail_cons, sub_self]

theorem lie_e₁e₃ : ⁅(e₁ : Hyperbolic K), (e₃ : Hyperbolic K)⁆ = e₃ := by
  rw [Hyperbolic.bracket, e₁_def, e₃_def]
  unfold Hyperbolic
  simp only [Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, mul_one, mul_zero, sub_zero, Matrix.cons_val_two,
    Matrix.tail_cons, sub_self]

theorem lie_e₂e₃ : ⁅(e₂ : Hyperbolic K), (e₃ : Hyperbolic K)⁆ = 0 := by
  rw [Hyperbolic.bracket, e₂_def, e₃_def]
  unfold Hyperbolic
  simp only [Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, mul_zero, mul_one, sub_self, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_self]

theorem ade₁_restr_id : ad_restr (e₁ : Hyperbolic K) = LinearMap.id := by
  ext y
  rw [ad_restr_apply]
  unfold adjoint
  simp only [ad_apply, LinearMap.id_coe, id_eq]
  obtain ⟨a, b, hy⟩ := commutator_repr.mp y.prop
  rw [← hy]
  simp only [lie_add, lie_smul]
  rw [lie_e₁e₂, lie_e₁e₃]

theorem ad_comm_restr {x : Hyperbolic K} (hx : x ∈ commutator K (Hyperbolic K)) : ad_restr (x : Hyperbolic K) = 0 := by
  ext y
  rw [ad_restr_apply]
  unfold adjoint
  simp only [ad_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero]
  obtain ⟨x₂, x₃, hx⟩ := commutator_repr.mp hx
  obtain ⟨y₂, y₃, hy⟩ := commutator_repr.mp y.prop
  rw [← hx, ← hy]
  simp only [lie_add, lie_smul, add_lie, smul_lie, lie_self, smul_zero, zero_add, add_zero]
  rw [← lie_skew, lie_e₂e₃]
  simp only [neg_zero, smul_zero, add_zero]

end Hyperbolic

end dim3_hyperbolic_lemmas

section dim3_family_lemmas

namespace Family

variable {K : Type*} [CommRing K] (α β : K)

/- In this section we study properties of the Lie algebra Family α β, with α ≠ 0. -/

def semidirectAux' : End K (Dim2.Abelian K) := {
  toFun := fun v ↦ ![α • v 1, v 0 + β • v 1]
  map_add' := by
    intro x y
    simp only [mkAbelian, Pi.add_apply, smul_eq_mul, mul_add, Matrix.add_cons,
      Matrix.head_cons, Matrix.tail_cons, Matrix.empty_add_empty]
    rw [add_add_add_comm]
  map_smul' := by
    intro a x
    simp only [mkAbelian, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Matrix.smul_cons, Matrix.smul_empty]
    rw [mul_left_comm α a, mul_left_comm β a, ← mul_add]
}

def semidirectAux : K →ₗ⁅K⁆ LieDerivation K (Dim2.Abelian K) (Dim2.Abelian K) :=
  LieHom.comp (Abelian.DerivationOfLinearMap K (Dim2.Abelian K)) (LieHom.smulRight (semidirectAux' α β))

def equivToSemidirect : Family K α β ≃ₗ⁅K⁆ K ⋉[semidirectAux α β] Dim2.Abelian K := {
  toFun := fun v ↦ ⟨v 0, ![v 1, v 2]⟩
  map_add' := by
    intro x y
    rw [Prod.add_def]
    simp only [Family, Pi.add_apply]
    ext
    · rfl
    · simp only [mkAbelian]
      ext i
      fin_cases i
      · simp only [Fin.zero_eta,
        Matrix.cons_val_zero, Pi.add_apply]
      · simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply]
  map_smul' := by
    intro a x
    rw [Prod.smul_def]
    simp only [Family, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ext
    · rfl
    · simp only [mkAbelian, Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty]
  map_lie' := by
    intro x y
    rw [Family.bracket, LieSemidirectProduct.bracket_def, semidirectAux, semidirectAux',
      ← LieHom.coe_toLinearMap]
    simp only [smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Bracket.bracket,
      LieHom.toLinearMap_comp, LinearMap.coe_comp, LieHom.coe_toLinearMap, LieHom.coe_smulRight,
      Function.comp_apply, LieHom.map_smul, LieDerivation.coe_smul, Abelian.DerivationCoeFun',
      LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Matrix.smul_cons, Matrix.smul_empty, add_zero]
    ext
    · simp only
      rw [mul_comm, sub_self]
    · simp only [mkAbelian]
      ext i
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.sub_apply]
        ring
      · simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply]
        ring_nf
  invFun := fun ⟨k, v⟩ ↦ ![k, v 0, v 1]
  left_inv := by
    intro x
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Heisenberg]
    exact List.ofFn_inj.mp rfl
  right_inv := by
    intro ⟨k, v⟩
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons]
    ext
    · rfl
    · simp only [mkAbelian]
      exact List.ofFn_inj.mp rfl
}

def M : Matrix (Fin 2) (Fin 2) K := ![
  ![0, α],
  ![1, β]
]

variable {α β : K}

theorem M_det {α β : K} : Matrix.det (M α β) = -α := by
  unfold M
  rw [Matrix.det_fin_two]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, zero_mul, mul_one, zero_sub]

theorem M_trace {α β : K} : Matrix.trace (M α β) = β := by
  unfold M
  rw [Matrix.trace_fin_two]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, zero_add]

def e₁ : Family K α β := ![1, 0, 0]
theorem e₁_def : (e₁ : Family K α β) = ![1, 0, 0] := by
  rfl
def e₂ : Family K α β := ![0, 1, 0]
theorem e₂_def : (e₂ : Family K α β) = ![0, 1, 0] := by
  rfl
def e₃ : Family K α β := ![0, 0, 1]
theorem e₃_def : (e₃ : Family K α β) = ![0, 0, 1] := by
  rfl

variable {K : Type*} [Field K] {α β : K}

theorem commutator_is_span_e₂e₃ (hα : α ≠ 0) : (commutator K (Family K α β)).toSubmodule = span K {e₂,e₃} := by
  let e₁α : Family K α β := ![α⁻¹, 0, 0]
  let e₂β : Family K α β := ![0, -β, 1]
  let e₁ : Family K α β := ![1, 0, 0]
  let e₂ : Family K α β := e₂
  let e₃ : Family K α β := e₃
  have e₂_bracket : ⁅e₁α ,e₂β⁆ = e₂ := by
    rw [Family.bracket]
    unfold e₂β e₁α e₂
    simp only [Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_one, mul_zero, sub_zero,
      Matrix.cons_val_one, mul_neg, add_neg_cancel, sub_self]
    simp_all only [ne_eq, isUnit_iff_ne_zero,not_false_eq_true, IsUnit.inv_mul_cancel,e₂_def, e₃_def]

  have e₃_bracket : ⁅e₁, e₂⁆ = e₃ := by
    rw [Family.bracket]
    unfold e₁ e₂ e₃
    simp only [Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_zero, sub_self, zero_mul,
      Matrix.cons_val_one, mul_one, zero_add, sub_zero, e₂_def, e₃_def]
  rw [commutator_eq_span]
  apply eq_of_le_of_le
  · rw [span_le]
    intro x ⟨y, z, h⟩
    simp only [Family.bracket] at h
    rw [← h]
    have cl : ![0, (y 0 * z 2 - y 2 * z 0) * α, (y 0 * z 2 - y 2 * z 0) * β + y 0 * z 1 - y 1 * z 0] =
      ((y 0 * z 2 - y 2 * z 0) * α) • e₂ + ((y 0 * z 2 - y 2 * z 0) * β + y 0 * z 1 - y 1 * z 0) • e₃ := by
      unfold e₂ e₃
      simp only [e₂_def, e₃_def]
      rw [Matrix.smul_vec3,Matrix.smul_vec3,Matrix.vec3_add]
      ext j; fin_cases j <;> simp
    symm at cl
    simp only [SetLike.mem_coe]
    rw [mem_span_pair]
    exact ⟨_, _, cl⟩
  · rw [span_le]
    trans {x | ∃ (y z: Family K α β), ⁅y, z⁆ = x}
    · intro e Be
      simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
      cases Be with
      | inl h => subst h; exact ⟨_, _, e₂_bracket⟩
      | inr h => subst h; exact ⟨_, _, e₃_bracket⟩
    · apply subset_span (R:=K) (M:=Family K α β) (s := {x | ∃ y z, ⁅y, z⁆ = x})

def B (α β : K) : Fin 2 → Family K α β := ![e₂, e₃]

theorem B_is_li_ambient : LinearIndependent K (M := Family K α β) (B α β) := by
      unfold B
      refine LinearIndependent.pair_iff.mpr ?_
      simp only [e₂_def, e₃_def]
      intro s t hst
      unfold Family at hst
      constructor
      · apply_fun (fun f ↦ f 1) at hst
        simp only [Matrix.smul_cons, smul_eq_mul, mul_zero, mul_one, Matrix.smul_empty, Fin.isValue,
          Pi.add_apply, Matrix.cons_val_one, Matrix.head_cons, add_zero, Pi.zero_apply,
          Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
          add_zero] at hst
        exact hst
      · apply_fun (fun f ↦ f 2) at hst
        simp only [Matrix.smul_cons, smul_eq_mul, mul_zero,
          mul_one, Matrix.smul_empty, Pi.add_apply, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_cons, zero_add, Pi.zero_apply] at hst
        exact hst

def e₁α : Family K α β := ![α⁻¹, 0, 0]
def e₂β : Family K α β := ![0, -β, 1]

theorem e₂_bracket {hα : α ≠ 0} : ⁅(e₁α : Family K α β), (e₂β : Family K α β)⁆ = e₂ := by
    rw [Family.bracket]
    unfold e₂β e₁α e₂
    simp only [Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_one, mul_zero, sub_zero,
      Matrix.cons_val_one, mul_neg, add_neg_cancel, sub_self]
    simp_all only [ne_eq, isUnit_iff_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel, e₂_def, e₃_def, hα]

theorem e₃_bracket : ⁅(e₁ : Family K α β), (e₂ : Family K α β)⁆ = e₃ := by
    rw [Family.bracket]
    unfold e₁ e₂ e₃
    simp only [Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_zero, sub_self, zero_mul,
      Matrix.cons_val_one, mul_one, zero_add, sub_zero, e₂_def, e₃_def]

lemma e₂_in_comm {hα : α ≠ 0} : e₂ ∈ commutator K (Family K α β) := by
    unfold e₂
    refine (LieSubmodule.mem_toSubmodule _).mp ?_
    rw [commutator_eq_span]
    have := subset_span (R := K) (M := Family K α β) (s := {x | ∃ (y z : Family K α β), ⁅y, z⁆ = x})
    exact (this ⟨_, _, e₂_bracket (α := α) (β := β) (hα := hα)⟩)

lemma e₃_in_comm : e₃ ∈ commutator K (Family K α β) := by
    unfold e₃
    refine (LieSubmodule.mem_toSubmodule _).mp ?_
    rw [commutator_eq_span]
    have := subset_span (R := K) (M := Family K α β) (s := {x | ∃ (y z : Family K α β), ⁅y, z⁆ = x})
    exact (this ⟨_, _, e₃_bracket⟩)

noncomputable def commutatorBasis (α β : K) (hα : α ≠ 0) : Basis (Fin 2) K (commutator K (Family K α β)) := by
  -- Basis are ![0,1,0] and ![0,0,1]
  let e₁α : Family K α β := ![α⁻¹, 0, 0]
  let e₂β : Family K α β := ![0, -β, 1]
  let e₁ : Family K α β := ![1, 0, 0]
  let e₂ : Family K α β := e₂
  let e₃ : Family K α β := e₃
  have e₂_bracket : ⁅e₁α, e₂β⁆ = e₂ := by
    rw [Family.bracket]
    unfold e₂β e₁α e₂
    simp only [Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_one, mul_zero, sub_zero,
      Matrix.cons_val_one, mul_neg, add_neg_cancel, sub_self]
    simp_all only [ne_eq, isUnit_iff_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel, e₂_def, e₃_def]

  have e₃_bracket : ⁅e₁, e₂⁆ = e₃ := by
    rw [Family.bracket]
    unfold e₁ e₂ e₃
    simp only [Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_zero, sub_self, zero_mul,
      Matrix.cons_val_one, mul_one, zero_add, sub_zero, e₂_def, e₃_def]

  have B_setrange {hα : α ≠ 0}  : Set.range (B α β) ⊆ commutator K (Family K α β) := by
    simp_all only [ne_eq, Matrix.range_cons,
      Matrix.range_empty, Set.union_empty, Set.union_singleton, B]
    intro e Be
    simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    cases Be with
    | inl h => subst h; simp_all only [SetLike.mem_coe, B, e₁α, e₂β, e₂, e₁, e₃, e₃_in_comm]
    | inr h => subst h; simp_all only [SetLike.mem_coe, B, e₁α, e₂β, e₂, e₁, e₃, e₂_in_comm (hα := hα)]

  have B_setrange_eq : Set.range (B α β) = {e₂, e₃} := by
    simp_all only [ne_eq, Matrix.range_cons,
      Matrix.range_empty, Set.union_empty, Set.union_singleton, B]
    simp_all only [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, e₁, e₂β, e₃, B, e₂, e₁α]
    ext x : 1
    simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, e₁, e₂β, e₃, B, e₂, e₁α]
    apply Iff.intro
    · intro a
      cases a with
      | inl h =>
        subst h
        simp_all only [or_true, e₁, e₂β, e₃, B, e₂, e₁α]
      | inr h_1 =>
        subst h_1
        simp_all only [true_or, e₁, e₂β, e₃, B, e₂, e₁α]
    · intro a
      cases a with
      | inl h =>
        subst h
        simp_all only [or_true, e₁, e₂β, e₃, B, e₂, e₁α]
      | inr h_1 =>
        subst h_1
        simp_all only [true_or, e₁, e₂β, e₃, B, e₂, e₁α]

  let B_is_li_comm := linearIndependent_from_ambient (K := K) (commutator K (Family K α β)) ![e₂, e₃] B_is_li_ambient (B_setrange (hα := hα))

  have : Set.range (Set.map_into_subtype (↑(↑(commutator K (Family K α β)))) (B α β) (B_setrange (hα:=hα) )) =
    ({⟨e₂, e₂_in_comm (hα := hα)⟩, ⟨e₃, e₃_in_comm⟩} : Set (↥(commutator K (Family K α β)))) := by
    unfold Set.range
    simp only [SetLike.coe_sort_coe, e₁, e₂β, e₁α]
    ext j
    constructor
    · intro j_in
      simp at j_in
      let ⟨y, hy⟩ := j_in
      have := Set.map_into_subtype_apply (↑(commutator K (Family K α β))) (B α β) (B_setrange (hα:=hα) ) (y)
      rw [hy] at this
      fin_cases y
      · simp at this
        unfold B at this
        subst hy
        simp only [Fin.zero_eta, Set.mem_insert_iff, Set.mem_singleton_iff]
        left
        simp at *
        apply Subtype.ext
        assumption
      · simp at this
        unfold B at this
        subst hy
        simp only [Fin.zero_eta, Set.mem_insert_iff, Set.mem_singleton_iff]
        right
        simp at *
        apply Subtype.ext
        assumption
    · intro e
      simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, e₁, e₂β, e₁α]
      rcases e with (e0 | e1)
      · subst e0
        simp only [Set.mem_setOf_eq, e₁, e₂β, e₁α]
        use 0
        apply Subtype.ext
        rw [Set.map_into_subtype_apply (↑(commutator K (Family K α β))) (B α β) (B_setrange) (0)]
        unfold B
        simp only [Matrix.cons_val_zero, e₁, e₂β, e₁α, e₂_def]
        unfold e₂
        simp only [e₂_def]
        exact hα
      · subst e1
        simp only [Set.mem_setOf_eq, e₁, e₂β, e₁α]
        use 1
        apply Subtype.ext
        rw [Set.map_into_subtype_apply (↑(commutator K (Family K α β))) (B α β) (B_setrange) (1)]
        unfold B
        simp only [Matrix.cons_val_one, Matrix.head_cons, e₁, e₂β, e₁α, e₃_def]
        unfold e₃
        simp only [e₃_def]
        simp []
        exact hα

  let B_basis : Basis (Fin 2) K (commutator K (Family K α β)) :=
    Basis.mk B_is_li_comm (by
      intro ⟨x, hx⟩
      simp only [mem_top, LieIdeal.toLieSubalgebra_toSubmodule, forall_const]
      norm_cast
      unfold B at this
      rw [this]
      have : x ∈ span K {e₂, e₃} := by
        rw [← commutator_is_span_e₂e₃ (hα := hα)]
        · exact hx
      rw [@mem_span_pair]
      rw [@mem_span_pair] at this
      let ⟨a, b, h⟩ := this
      use a
      use b
      apply Subtype.ext
      simp only [SetLike.mk_smul_mk, AddMemClass.mk_add_mk]
      exact h)

  exact B_basis

theorem dim_commutator {hα : α ≠ 0} : finrank K (commutator K (Family K α β)) = 2 := by
  rw [finrank_eq_card_basis (commutatorBasis α β hα), Fintype.card_fin]

theorem B_basis_0 {hα : α ≠ 0} : ((commutatorBasis α β hα) 0).val = (e₂ : Family K α β) := by
  simp only [commutatorBasis, e₂, Basis.coe_mk]
  rfl

theorem B_basis_1 {hα : α ≠ 0} : ((commutatorBasis α β hα) 1).val = (e₃ : Family K α β) := by
  simp only [commutatorBasis, e₃, Basis.coe_mk]
  rfl

theorem B_basis_repr {hα : α ≠ 0} {x : commutator K (Family K α β)} : (commutatorBasis α β hα).repr x = ![x.val 1, x.val 2] := by
  let ⟨x, hx⟩ := x
  have h_repr := Basis.repr_fin_two (commutatorBasis α β hα) ⟨x, hx⟩
  have : x ∈ span K {e₂, e₃} := by
    rw [← commutator_is_span_e₂e₃ (hα := hα)]
    exact hx
  let ⟨a, b, h⟩ := mem_span_pair.mp this
  have w := h
  unfold e₂ e₃ at h
  rw [@Matrix.smul_vec3, @Matrix.smul_vec3, Matrix.vec3_add] at h
  simp at h
  symm at h
  have x00 : x 0 = 0 := by
    apply_fun (fun x => x 0) at h
    exact h
  have x1a : x 1 = a := by
    apply_fun (fun x => x 1) at h
    exact h
  have x2b : x 2 = b := by
    apply_fun (fun x => x 2) at h
    exact h
  have h_repr := Basis.repr_fin_two (commutatorBasis α β hα) ⟨x, hx⟩
  rw [Subtype.ext_iff] at h_repr
  simp only [LieSubmodule.coe_add, SetLike.val_smul] at h_repr
  rw [h_repr] at w
  rw [B_basis_0, B_basis_1] at w
  let B : Fin 2 → Family K α β := ![e₂, e₃]
  have B_is_li_ambient : LinearIndependent K (M := Family K α β) B := by
    unfold B
    refine LinearIndependent.pair_iff.mpr ?_
    simp only [e₂_def, e₃_def]
    intro s t hst
    unfold Family at hst
    constructor
    · apply_fun (fun f ↦ f 1) at hst
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.smul_cons, smul_eq_mul, mul_zero,
        mul_one, Matrix.smul_empty, Fin.isValue, Pi.add_apply, Matrix.cons_val_one,
        Matrix.cons_val_zero, add_zero, Pi.zero_apply] at hst
      exact hst
    · apply_fun (fun f ↦ f 2) at hst
      simp only [Matrix.smul_cons, smul_eq_mul, mul_zero,
        mul_one, Matrix.smul_empty, Pi.add_apply, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, zero_add, Pi.zero_apply] at hst
      exact hst
  obtain ⟨a_eq, b_eq⟩ := LinearIndependent.eq_of_pair (R := K) (M := Family K α β) (x := e₂) (y := e₃) B_is_li_ambient w
  rw [a_eq] at x1a
  rw [b_eq] at x2b
  norm_cast
  rw [x1a, x2b]
  ext j
  fin_cases j
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
  · simp only [Fin.mk_one, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

def ade₁ := ad K (Family K α β) e₁

def adjoint (x : Family K α β) := ad K (Family K α β) x

theorem ade₁_pc : ∀ x ∈ (commutator K (Family K α β)), ade₁ x ∈ (commutator K (Family K α β)) := by
  intro x hx
  unfold ade₁
  simp only [ad_apply]
  exact lie_mem_commutator e₁ x

theorem ad_pc (x : Family K α β) : ∀ y ∈ (commutator K (Family K α β)), (adjoint x) y ∈ (commutator K (Family K α β)) := by
  intro y hy
  unfold adjoint
  simp only [ad_apply]
  exact lie_mem_commutator x y

def ad_restr (x : Family K α β) : (commutator K (Family K α β)) →ₗ[K] (commutator K (Family K α β)) :=
  LinearMap.restrict (adjoint x) (ad_pc x)

def ade₁_restr (α β : K) := ad_restr e₁ (α:=α) (β:=β)

theorem ad_restr_apply (x : Family K α β)  (y : Family K α β) (hy : y ∈ (commutator K (Family K α β))) :
    ad_restr x (⟨y, hy⟩ : (commutator K (Family K α β))) = ⟨adjoint x y, ad_pc x y hy⟩ :=
  rfl

theorem M_is_ade₁_restr {hα : α ≠ 0} : LinearMap.toMatrix (commutatorBasis α β hα) (commutatorBasis α β hα) (ade₁_restr α β) = M α β := by
    let e₁α : Family K α β := ![α⁻¹, 0, 0]
    let e₂β : Family K α β := ![0, -β, 1]
    unfold ade₁_restr
    unfold M
    ext i j
    simp only [LinearMap.toMatrix_apply]
    fin_cases j
    · simp
      rw [ad_restr_apply]
      unfold adjoint
      simp only [ad_apply]
      simp only [B_basis_0, e₂_def]
      simp only [Family.bracket]
      rw [B_basis_repr]
      simp only [Matrix.cons_val_zero,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_zero, sub_self, zero_mul,
        Matrix.cons_val_one, mul_one, zero_add, sub_zero, e₁, e₂β, e₃, e₂, commutatorBasis, e₁α]
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
    · simp
      rw [ad_restr_apply]
      unfold adjoint
      simp only [ad_apply]
      simp only [B_basis_1, e₃_def]
      simp only [Family.bracket]
      rw [B_basis_repr]

      simp only [Matrix.cons_val_zero,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_one, mul_zero, sub_zero,
        one_mul, Matrix.cons_val_one, add_zero]
      unfold e₁
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero,one_mul]
      · simp only [Matrix.cons_val_zero, one_mul, Fin.mk_one, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const]

theorem tr_ade₁ (hα : α ≠ 0) : LinearMap.trace _ (commutator K (Family K α β)) (ade₁_restr α β) = β :=by
    rw [LinearMap.trace_eq_matrix_trace K (commutatorBasis α β hα) (ade₁_restr α β)]
    rw [M_is_ade₁_restr]
    exact M_trace

theorem det_ade₁ (hα : α ≠ 0) : LinearMap.det (ade₁_restr α β) = -α :=by
    rw [← LinearMap.det_toMatrix (ι:=Fin 2) (f:=(ade₁_restr α β)) (commutatorBasis α β hα)]
    rw[M_is_ade₁_restr]
    exact M_det

theorem e₁_not_in_comm (hα : α ≠ 0) : e₁ ∉ commutator K (Family K α β) := by
    intro hb0
    rw [e₁_def] at hb0
    have hb0S: ![1, 0, 0] ∈ (commutator K (Family K α β)).toSubmodule := by
      simp_all only [ne_eq, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, Nat.reduceAdd,
        LieSubmodule.mem_toSubmodule]
    rw [commutator_is_span_e₂e₃ (α:=α) (β:=β) (hα:=hα)] at hb0S
    rw [@mem_span_pair] at hb0S
    let ⟨a, b, h⟩ := hb0S
    unfold e₂ e₃ at h
    rw [@Matrix.smul_vec3, @Matrix.smul_vec3, Matrix.vec3_add] at h
    simp at h
    have : ![0, a, b] 0 = ![1, 0, 0] 0 := by
      rw [h]
    simp at this

end Family
end dim3_family_lemmas
end Dim3
end LieAlgebra
